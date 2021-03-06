/*

# Collect phase

The collect phase of type check has the job of visiting all items,
determining their type, and writing that type into the `tcx.tcache`
table.  Despite its name, this table does not really operate as a
*cache*, at least not for the types of items defined within the
current crate: we assume that after the collect phase, the types of
all local items will be present in the table.

Unlike most of the types that are present in Rust, the types computed
for each item are in fact polytypes.  In "layman's terms", this means
that they are generic types that may have type parameters (more
mathematically phrased, they are universally quantified over a set of
type parameters).  Polytypes are represented by an instance of
`ty::ty_param_bounds_and_ty`.  This combines the core type along with
a list of the bounds for each parameter.  Type parameters themselves
are represented as `ty_param()` instances.

*/

use astconv::{ast_conv, ty_of_fn_decl, ty_of_arg, ast_ty_to_ty};
use ast_util::trait_method_to_ty_method;
use rscope::*;

fn collect_item_types(ccx: @crate_ctxt, crate: @ast::crate) {

    // FIXME (#2592): hooking into the "intrinsic" root module is crude.
    // There ought to be a better approach. Attributes?

    for crate.node.module.items.each |crate_item| {
        if crate_item.ident
            == syntax::parse::token::special_idents::intrinsic {

            match crate_item.node {
              ast::item_mod(m) => {
                for m.items.each |intrinsic_item| {
                    let def_id = { crate: ast::local_crate,
                                  node: intrinsic_item.id };
                    let substs = {self_r: None, self_ty: None, tps: ~[]};

                    match intrinsic_item.node {
                      ast::item_trait(*) => {
                        let ty = ty::mk_trait(ccx.tcx, def_id, substs,
                                              ty::vstore_box);
                        ccx.tcx.intrinsic_defs.insert
                            (intrinsic_item.ident, (def_id, ty));
                      }

                      ast::item_enum(*) => {
                        let ty = ty::mk_enum(ccx.tcx, def_id, substs);
                        ccx.tcx.intrinsic_defs.insert
                            (intrinsic_item.ident, (def_id, ty));
                      }

                      _ => {}
                    }
                }
              }
              _ => { }
            }
            break;
        }
    }

    visit::visit_crate(*crate, (), visit::mk_simple_visitor(@{
        visit_item: |a|convert(ccx, a),
        visit_foreign_item: |a|convert_foreign(ccx, a),
        .. *visit::default_simple_visitor()
    }));
}

impl @crate_ctxt {
    fn to_ty<RS: region_scope copy owned>(
        rs: RS, ast_ty: @ast::ty) -> ty::t {

        ast_ty_to_ty(self, rs, ast_ty)
    }
}

impl @crate_ctxt: ast_conv {
    fn tcx() -> ty::ctxt { self.tcx }
    fn ccx() -> @crate_ctxt { self }

    fn get_item_ty(id: ast::def_id) -> ty::ty_param_bounds_and_ty {
        if id.crate != ast::local_crate {
            csearch::get_type(self.tcx, id)
        } else {
            match self.tcx.items.find(id.node) {
              Some(ast_map::node_item(item, _)) => {
                ty_of_item(self, item)
              }
              Some(ast_map::node_foreign_item(foreign_item, _, _)) => {
                ty_of_foreign_item(self, foreign_item)
              }
              x => {
                self.tcx.sess.bug(fmt!("unexpected sort of item \
                                        in get_item_ty(): %?", x));
              }
            }
        }
    }

    fn ty_infer(span: span) -> ty::t {
        self.tcx.sess.span_bug(span,
                               ~"found `ty_infer` in unexpected place");
    }
}

fn get_enum_variant_types(ccx: @crate_ctxt,
                          enum_ty: ty::t,
                          variants: ~[ast::variant],
                          ty_params: ~[ast::ty_param],
                          rp: Option<ty::region_variance>) {
    let tcx = ccx.tcx;

    // Create a set of parameter types shared among all the variants.
    for variants.each |variant| {
        // Nullary enum constructors get turned into constants; n-ary enum
        // constructors get turned into functions.
        let result_ty;
        match variant.node.kind {
            ast::tuple_variant_kind(args) if args.len() > 0 => {
                let rs = type_rscope(rp);
                let args = args.map(|va| {
                    let arg_ty = ccx.to_ty(rs, va.ty);
                    {mode: ast::expl(ast::by_copy), ty: arg_ty}
                });
                result_ty = Some(ty::mk_fn(tcx,
                                           {purity: ast::pure_fn,
                                            proto: ty::proto_vstore
                                                (ty::vstore_box),
                                            bounds: @~[],
                                            inputs: args,
                                            output: enum_ty,
                                            ret_style: ast::return_val}));
            }
            ast::tuple_variant_kind(_) | ast::struct_variant_kind(_) => {
                result_ty = Some(enum_ty);
            }
            ast::enum_variant_kind(enum_definition) => {
                get_enum_variant_types(ccx, enum_ty, enum_definition.variants,
                                       ty_params, rp);
                result_ty = None;
            }
        };

        match result_ty {
            None => {}
            Some(result_ty) => {
                let tpt = {bounds: ty_param_bounds(ccx, ty_params),
                           region_param: rp,
                           ty: result_ty};
                tcx.tcache.insert(local_def(variant.node.id), tpt);
                write_ty_to_tcx(tcx, variant.node.id, result_ty);
            }
        }
    }
}

fn ensure_trait_methods(ccx: @crate_ctxt, id: ast::node_id, trait_ty: ty::t) {
    fn store_methods<T>(ccx: @crate_ctxt, id: ast::node_id,
                        stuff: ~[T], f: fn@(T) -> ty::method) {
        ty::store_trait_methods(ccx.tcx, id, @vec::map(stuff, f));
    }

    fn make_static_method_ty(ccx: @crate_ctxt,
                             am: ast::ty_method,
                             rp: Option<ty::region_variance>,
                             m: ty::method,
                             // Take this as an argument b/c we may check
                             // the impl before the trait.
                             trait_ty: ty::t,
                             trait_bounds: @~[ty::param_bounds]) {
        // We need to create a typaram that replaces self. This param goes
        // *in between* the typarams from the trait and those from the
        // method (since its bound can depend on the trait? or
        // something like that).

        // build up a subst that shifts all of the parameters over
        // by one and substitute in a new type param for self

        let dummy_defid = {crate: 0, node: 0};

        let non_shifted_trait_tps = do vec::from_fn(trait_bounds.len()) |i| {
            ty::mk_param(ccx.tcx, i, dummy_defid)
        };
        let self_param = ty::mk_param(ccx.tcx, trait_bounds.len(),
                                      dummy_defid);
        let shifted_method_tps = do vec::from_fn(m.tps.len()) |i| {
            ty::mk_param(ccx.tcx, i + 1, dummy_defid)
        };

        let substs = { self_r: None, self_ty: Some(self_param),
                       tps: non_shifted_trait_tps + shifted_method_tps };
        let ty = ty::subst(ccx.tcx, &substs, ty::mk_fn(ccx.tcx, m.fty));
        let bounds = @(*trait_bounds + ~[@~[ty::bound_trait(trait_ty)]]
                       + *m.tps);
        ccx.tcx.tcache.insert(local_def(am.id),
                              {bounds: bounds,
                               region_param: rp,
                               ty: ty});
    }


    let tcx = ccx.tcx;
    let region_paramd = tcx.region_paramd_items.find(id);
    match tcx.items.get(id) {
      ast_map::node_item(@{node: ast::item_trait(params, _, ms), _}, _) => {
        store_methods::<ast::trait_method>(ccx, id, ms, |m| {
            let trait_bounds = ty_param_bounds(ccx, params);
            let ty_m = trait_method_to_ty_method(m);
            let method_ty = ty_of_ty_method(ccx, ty_m, region_paramd);
            if ty_m.self_ty.node == ast::sty_static {
                make_static_method_ty(ccx, ty_m, region_paramd,
                                      method_ty, trait_ty, trait_bounds);
            }
            method_ty
        });
      }
      ast_map::node_item(@{node: ast::item_class(struct_def, _), _}, _) => {
        // All methods need to be stored, since lookup_method
        // relies on the same method cache for self-calls
        store_methods::<@ast::method>(ccx, id, struct_def.methods, |m| {
            ty_of_method(ccx, m, region_paramd)
        });
      }
      _ => { /* Ignore things that aren't traits or classes */ }
    }
}

/**
 * Checks that a method from an impl/class conforms to the signature of
 * the same method as declared in the trait.
 *
 * # Parameters
 *
 * - impl_m: the method in the impl
 * - impl_tps: the type params declared on the impl itself (not the method!)
 * - trait_m: the method in the trait
 * - trait_substs: the substitutions used on the type of the trait
 * - self_ty: the self type of the impl
 */
fn compare_impl_method(tcx: ty::ctxt, sp: span,
                       impl_m: ty::method, impl_tps: uint,
                       trait_m: ty::method, trait_substs: ty::substs,
                       self_ty: ty::t) {

    if impl_m.fty.purity != trait_m.fty.purity {
        tcx.sess.span_err(
            sp, fmt!("method `%s`'s purity does \
                          not match the trait method's \
                          purity", tcx.sess.str_of(impl_m.ident)));
    }

    // is this check right?
    if impl_m.self_ty != trait_m.self_ty {
        tcx.sess.span_err(
            sp, fmt!("method `%s`'s self type does \
                          not match the trait method's \
                          self type", tcx.sess.str_of(impl_m.ident)));
    }

    if impl_m.tps != trait_m.tps {
        tcx.sess.span_err(sp, ~"method `" + tcx.sess.str_of(trait_m.ident) +
                          ~"` has an incompatible set of type parameters");
        return;
    }

    if vec::len(impl_m.fty.inputs) != vec::len(trait_m.fty.inputs) {
        tcx.sess.span_err(sp,fmt!("method `%s` has %u parameters \
                                   but the trait has %u",
                                   tcx.sess.str_of(trait_m.ident),
                                   vec::len(impl_m.fty.inputs),
                                   vec::len(trait_m.fty.inputs)));
        return;
    }

    // Perform substitutions so that the trait/impl methods are expressed
    // in terms of the same set of type/region parameters:
    // - replace trait type parameters with those from `trait_substs`
    // - replace method parameters on the trait with fresh, dummy parameters
    //   that correspond to the parameters we will find on the impl
    // - replace self region with a fresh, dummy region
    let dummy_self_r = ty::re_free(0, ty::br_self);
    let impl_fty = {
        let impl_fty = ty::mk_fn(tcx, impl_m.fty);
        replace_bound_self(tcx, impl_fty, dummy_self_r)
    };
    let trait_fty = {
        let dummy_tps = do vec::from_fn((*trait_m.tps).len()) |i| {
            // hack: we don't know the def id of the impl tp, but it
            // is not important for unification
            ty::mk_param(tcx, i + impl_tps, {crate: 0, node: 0})
        };
        let substs = {
            self_r: Some(dummy_self_r),
            self_ty: Some(self_ty),
            tps: vec::append(trait_substs.tps, dummy_tps)
        };
        let trait_fty = ty::mk_fn(tcx, trait_m.fty);
        ty::subst(tcx, &substs, trait_fty)
    };
    require_same_types(
        tcx, None, false, sp, impl_fty, trait_fty,
        || ~"method `" + tcx.sess.str_of(trait_m.ident)
           + ~"` has an incompatible type");
    return;

    // Replaces bound references to the self region with `with_r`.
    fn replace_bound_self(tcx: ty::ctxt, ty: ty::t,
                          with_r: ty::region) -> ty::t {
        do ty::fold_regions(tcx, ty) |r, _in_fn| {
            if r == ty::re_bound(ty::br_self) {with_r} else {r}
        }
    }
}

fn check_methods_against_trait(ccx: @crate_ctxt,
                               tps: ~[ast::ty_param],
                               rp: Option<ty::region_variance>,
                               selfty: ty::t,
                               a_trait_ty: @ast::trait_ref,
                               impl_ms: ~[converted_method]) {

    let tcx = ccx.tcx;
    let (did, tpt) = instantiate_trait_ref(ccx, a_trait_ty, rp);
    if did.crate == ast::local_crate {
        ensure_trait_methods(ccx, did.node, tpt.ty);
    }
    for vec::each(*ty::trait_methods(tcx, did)) |trait_m| {
        match vec::find(impl_ms, |impl_m| trait_m.ident == impl_m.mty.ident) {
          Some({mty: impl_m, span, _}) => {
            compare_impl_method(
                ccx.tcx, span, impl_m, vec::len(tps),
                trait_m, tpt.substs, selfty);
          }
          None => {
              // If we couldn't find an implementation for trait_m in
              // the impl, then see if there was a default
              // implementation in the trait itself.  If not, raise a
              // "missing method" error.

              match tcx.items.get(did.node) {
                ast_map::node_item(
                    @{node: ast::item_trait(_, _, trait_methods), _}, _) => {
                  let (_, provided_methods) =
                      split_trait_methods(trait_methods);

                  match vec::find(provided_methods, |provided_method|
                                provided_method.ident == trait_m.ident) {
                    Some(_) => {
                      // If there's a provided method with the name we
                      // want, then we're fine; nothing else to do.
                    }
                    None => {
                      tcx.sess.span_err(
                          a_trait_ty.path.span,
                          fmt!("missing method `%s`",
                               tcx.sess.str_of(trait_m.ident)));
                    }
                  }
                }
                _ => {
                    tcx.sess.bug(~"check_methods_against_trait(): trait_ref \
                                   didn't refer to a trait");
                }
              }
          }
        } // alt
    } // |trait_m|
} // fn

fn convert_field(ccx: @crate_ctxt,
                 rp: Option<ty::region_variance>,
                 bounds: @~[ty::param_bounds],
                 v: @ast::struct_field) {
    let tt = ccx.to_ty(type_rscope(rp), v.node.ty);
    write_ty_to_tcx(ccx.tcx, v.node.id, tt);
    /* add the field to the tcache */
    ccx.tcx.tcache.insert(local_def(v.node.id),
                          {bounds: bounds,
                           region_param: rp,
                           ty: tt});
}

type converted_method = {mty: ty::method, id: ast::node_id, span: span};

fn convert_methods(ccx: @crate_ctxt,
                   ms: ~[@ast::method],
                   rp: Option<ty::region_variance>,
                   rcvr_bounds: @~[ty::param_bounds]) -> ~[converted_method] {

    let tcx = ccx.tcx;
    do vec::map(ms) |m| {
        let bounds = ty_param_bounds(ccx, m.tps);
        let mty = ty_of_method(ccx, m, rp);
        let fty = ty::mk_fn(tcx, mty.fty);
        tcx.tcache.insert(
            local_def(m.id),

            // n.b.: the type of a method is parameterized by both
            // the tps on the receiver and those on the method itself
            {bounds: @(vec::append(*rcvr_bounds, *bounds)),
             region_param: rp,
             ty: fty});
        write_ty_to_tcx(tcx, m.id, fty);
        {mty: mty, id: m.id, span: m.span}
    }
}

fn convert(ccx: @crate_ctxt, it: @ast::item) {
    let tcx = ccx.tcx;
    let rp = tcx.region_paramd_items.find(it.id);
    debug!("convert: item %s with id %d rp %?",
           tcx.sess.str_of(it.ident), it.id, rp);
    match it.node {
      // These don't define types.
      ast::item_foreign_mod(_) | ast::item_mod(_) => {}
      ast::item_enum(enum_definition, ty_params) => {
        let tpt = ty_of_item(ccx, it);
        write_ty_to_tcx(tcx, it.id, tpt.ty);
        get_enum_variant_types(ccx, tpt.ty, enum_definition.variants,
                               ty_params, rp);
      }
      ast::item_impl(tps, trait_ref, selfty, ms) => {
        let i_bounds = ty_param_bounds(ccx, tps);
        let selfty = ccx.to_ty(type_rscope(rp), selfty);
        write_ty_to_tcx(tcx, it.id, selfty);
        tcx.tcache.insert(local_def(it.id),
                          {bounds: i_bounds,
                           region_param: rp,
                           ty: selfty});

        let cms = convert_methods(ccx, ms, rp, i_bounds);
        for trait_ref.each |t| {
            check_methods_against_trait(ccx, tps, rp, selfty, t, cms);
        }
      }
      ast::item_trait(tps, _, trait_methods) => {
        let tpt = ty_of_item(ccx, it);
        debug!("item_trait(it.id=%d, tpt.ty=%s)",
               it.id, ty_to_str(tcx, tpt.ty));
        write_ty_to_tcx(tcx, it.id, tpt.ty);
        ensure_trait_methods(ccx, it.id, tpt.ty);

        let (_, provided_methods) = split_trait_methods(trait_methods);
        let {bounds, _} = mk_substs(ccx, tps, rp);
        let _cms = convert_methods(ccx, provided_methods, rp, bounds);
        // FIXME (#2616): something like this, when we start having
        // trait inheritance?
        // for trait_ref.each |t| {
        // check_methods_against_trait(ccx, tps, rp, selfty, t, cms);
        // }
      }
      ast::item_class(struct_def, tps) => {
        // Write the class type
        let tpt = ty_of_item(ccx, it);
        write_ty_to_tcx(tcx, it.id, tpt.ty);
        tcx.tcache.insert(local_def(it.id), tpt);

        convert_struct(ccx, rp, struct_def, tps, tpt, it.id);
      }
      _ => {
        // This call populates the type cache with the converted type
        // of the item in passing. All we have to do here is to write
        // it into the node type table.
        let tpt = ty_of_item(ccx, it);
        write_ty_to_tcx(tcx, it.id, tpt.ty);
      }
    }
}

fn convert_struct(ccx: @crate_ctxt,
                  rp: Option<ty::region_variance>,
                  struct_def: @ast::struct_def,
                  tps: ~[ast::ty_param],
                  tpt: ty::ty_param_bounds_and_ty,
                  id: ast::node_id) {
    let tcx = ccx.tcx;
    do option::iter(struct_def.ctor) |ctor| {
        // Write the ctor type
        let t_args = ctor.node.dec.inputs.map(
            |a| ty_of_arg(ccx, type_rscope(rp), a, None) );
        let t_res = ty::mk_class(
            tcx, local_def(id),
            {self_r: rscope::bound_self_region(rp),
             self_ty: None,
             tps: ty::ty_params_to_tys(tcx, tps)});
        let t_ctor = ty::mk_fn(
            tcx, {purity: ast::impure_fn,
                  proto: ty::proto_vstore(ty::vstore_slice(ty::re_static)),
                  bounds: @~[],
                  inputs: t_args,
                  output: t_res,
                  ret_style: ast::return_val});
        write_ty_to_tcx(tcx, ctor.node.id, t_ctor);
        tcx.tcache.insert(local_def(ctor.node.id),
                          {bounds: tpt.bounds,
                           region_param: rp,
                           ty: t_ctor});
    }

    do option::iter(struct_def.dtor) |dtor| {
        // Write the dtor type
        let t_dtor = ty::mk_fn(
            tcx,
            ty_of_fn_decl(ccx, type_rscope(rp), ast::proto_bare,
                          ast::impure_fn, @~[],
                          ast_util::dtor_dec(), None, dtor.span));
        write_ty_to_tcx(tcx, dtor.node.id, t_dtor);
        tcx.tcache.insert(local_def(dtor.node.id),
                          {bounds: tpt.bounds,
                           region_param: rp,
                           ty: t_dtor});
    };
    ensure_trait_methods(ccx, id, tpt.ty);

    // Write the type of each of the members
    for struct_def.fields.each |f| {
       convert_field(ccx, rp, tpt.bounds, f);
    }
    let {bounds, substs} = mk_substs(ccx, tps, rp);
    let selfty = ty::mk_class(tcx, local_def(id), substs);
    let cms = convert_methods(ccx, struct_def.methods, rp, bounds);
    for struct_def.traits.each |trait_ref| {
        check_methods_against_trait(ccx, tps, rp, selfty, trait_ref, cms);
        // trait_ref.impl_id represents (class, trait) pair
        write_ty_to_tcx(tcx, trait_ref.impl_id, tpt.ty);
        tcx.tcache.insert(local_def(trait_ref.impl_id), tpt);
    }
}

fn convert_foreign(ccx: @crate_ctxt, i: @ast::foreign_item) {
    // As above, this call populates the type table with the converted
    // type of the foreign item. We simply write it into the node type
    // table.
    let tpt = ty_of_foreign_item(ccx, i);
    write_ty_to_tcx(ccx.tcx, i.id, tpt.ty);
    ccx.tcx.tcache.insert(local_def(i.id), tpt);
}

fn ty_of_method(ccx: @crate_ctxt,
                m: @ast::method,
                rp: Option<ty::region_variance>) -> ty::method {
    {ident: m.ident,
     tps: ty_param_bounds(ccx, m.tps),
     fty: ty_of_fn_decl(ccx, type_rscope(rp), ast::proto_bare,
                        m.purity, @~[],
                        m.decl, None, m.span),
     self_ty: m.self_ty.node,
     vis: m.vis}
}

fn ty_of_ty_method(self: @crate_ctxt,
                   m: ast::ty_method,
                   rp: Option<ty::region_variance>) -> ty::method {
    {ident: m.ident,
     tps: ty_param_bounds(self, m.tps),
     fty: ty_of_fn_decl(self, type_rscope(rp), ast::proto_bare, m.purity,
                        @~[], m.decl, None, m.span),
     // assume public, because this is only invoked on trait methods
     self_ty: m.self_ty.node,
     vis: ast::public}
}

/*
  Instantiates the path for the given trait reference, assuming that
  it's bound to a valid trait type. Returns the def_id for the defining
  trait. Fails if the type is a type other than an trait type.
 */
fn instantiate_trait_ref(ccx: @crate_ctxt, t: @ast::trait_ref,
                         rp: Option<ty::region_variance>)
    -> (ast::def_id, ty_param_substs_and_ty) {

    let sp = t.path.span, err = ~"can only implement trait types",
        sess = ccx.tcx.sess;

    let rscope = type_rscope(rp);

    match lookup_def_tcx(ccx.tcx, t.path.span, t.ref_id) {
      ast::def_ty(t_id) => {
        let tpt = astconv::ast_path_to_ty(ccx, rscope, t_id, t.path,
                                          t.ref_id);
        match ty::get(tpt.ty).struct {
           ty::ty_trait(*) => {
              (t_id, tpt)
           }
           _ => sess.span_fatal(sp, err),
        }
      }
      _ => sess.span_fatal(sp, err)
    }
}

fn ty_of_item(ccx: @crate_ctxt, it: @ast::item)
    -> ty::ty_param_bounds_and_ty {

    let def_id = local_def(it.id);
    let tcx = ccx.tcx;
    match tcx.tcache.find(def_id) {
      Some(tpt) => return tpt,
      _ => {}
    }
    let rp = tcx.region_paramd_items.find(it.id);
    match it.node {
      ast::item_const(t, _) => {
        let typ = ccx.to_ty(empty_rscope, t);
        let tpt = no_params(typ);
        tcx.tcache.insert(local_def(it.id), tpt);
        return tpt;
      }
      ast::item_fn(decl, purity, tps, _) => {
        let bounds = ty_param_bounds(ccx, tps);
        let tofd = ty_of_fn_decl(ccx, empty_rscope,
                                 ast::proto_bare, purity, @~[],
                                 decl, None, it.span);
        let tpt = {bounds: bounds,
                   region_param: None,
                   ty: ty::mk_fn(ccx.tcx, tofd)};
        debug!("type of %s (id %d) is %s",
               tcx.sess.str_of(it.ident), it.id, ty_to_str(tcx, tpt.ty));
        ccx.tcx.tcache.insert(local_def(it.id), tpt);
        return tpt;
      }
      ast::item_ty(t, tps) => {
        match tcx.tcache.find(local_def(it.id)) {
          Some(tpt) => return tpt,
          None => { }
        }

        let rp = tcx.region_paramd_items.find(it.id);
        let tpt = {
            let ty = {
                let t0 = ccx.to_ty(type_rscope(rp), t);
                // Do not associate a def id with a named, parameterized type
                // like "foo<X>".  This is because otherwise ty_to_str will
                // print the name as merely "foo", as it has no way to
                // reconstruct the value of X.
                if !vec::is_empty(tps) { t0 } else {
                    ty::mk_with_id(tcx, t0, def_id)
                }
            };
            {bounds: ty_param_bounds(ccx, tps),
             region_param: rp,
             ty: ty}
        };

        tcx.tcache.insert(local_def(it.id), tpt);
        return tpt;
      }
      ast::item_enum(_, tps) => {
        // Create a new generic polytype.
        let {bounds, substs} = mk_substs(ccx, tps, rp);
        let t = ty::mk_enum(tcx, local_def(it.id), substs);
        let tpt = {bounds: bounds,
                   region_param: rp,
                   ty: t};
        tcx.tcache.insert(local_def(it.id), tpt);
        return tpt;
      }
      ast::item_trait(tps, _, _) => {
        let {bounds, substs} = mk_substs(ccx, tps, rp);
        let t = ty::mk_trait(tcx, local_def(it.id), substs, ty::vstore_box);
        let tpt = {bounds: bounds,
                   region_param: rp,
                   ty: t};
        tcx.tcache.insert(local_def(it.id), tpt);
        return tpt;
      }
      ast::item_class(_, tps) => {
          let {bounds,substs} = mk_substs(ccx, tps, rp);
          let t = ty::mk_class(tcx, local_def(it.id), substs);
          let tpt = {bounds: bounds,
                     region_param: rp,
                     ty: t};
          tcx.tcache.insert(local_def(it.id), tpt);
          return tpt;
      }
      ast::item_impl(*) | ast::item_mod(_) |
      ast::item_foreign_mod(_) => fail,
      ast::item_mac(*) => fail ~"item macros unimplemented"
    }
}

fn ty_of_foreign_item(ccx: @crate_ctxt, it: @ast::foreign_item)
    -> ty::ty_param_bounds_and_ty {
    match it.node {
      ast::foreign_item_fn(fn_decl, purity, params) => {
        return ty_of_foreign_fn_decl(ccx, fn_decl, purity, params,
                                     local_def(it.id));
      }
      ast::foreign_item_const(t) => {
        let rb = in_binding_rscope(empty_rscope);
        return {
            bounds: @~[],
            region_param: None,
            ty: ast_ty_to_ty(ccx, rb, t)
        };
      }
    }
}

fn compute_bounds(ccx: @crate_ctxt,
                  ast_bounds: @~[ast::ty_param_bound]) -> ty::param_bounds {
    @do vec::flat_map(*ast_bounds) |b| {
        match b {
          ast::bound_send => ~[ty::bound_send],
          ast::bound_copy => ~[ty::bound_copy],
          ast::bound_const => ~[ty::bound_const],
          ast::bound_owned => ~[ty::bound_owned],
          ast::bound_trait(t) => {
            let ity = ast_ty_to_ty(ccx, empty_rscope, t);
            match ty::get(ity).struct {
              ty::ty_trait(*) => {
                ~[ty::bound_trait(ity)]
              }
              _ => {
                ccx.tcx.sess.span_err(
                    t.span, ~"type parameter bounds must be \
                              trait types");
                ~[]
              }
            }
          }
        }
    }
}

fn ty_param_bounds(ccx: @crate_ctxt,
                   params: ~[ast::ty_param]) -> @~[ty::param_bounds] {


    @do params.map |param| {
        match ccx.tcx.ty_param_bounds.find(param.id) {
          Some(bs) => bs,
          None => {
            let bounds = compute_bounds(ccx, param.bounds);
            ccx.tcx.ty_param_bounds.insert(param.id, bounds);
            bounds
          }
        }
    }
}

fn ty_of_foreign_fn_decl(ccx: @crate_ctxt,
                         decl: ast::fn_decl,
                         purity: ast::purity,
                         ty_params: ~[ast::ty_param],
                         def_id: ast::def_id) -> ty::ty_param_bounds_and_ty {

    let bounds = ty_param_bounds(ccx, ty_params);
    let rb = in_binding_rscope(empty_rscope);
    let input_tys = decl.inputs.map(|a| ty_of_arg(ccx, rb, a, None) );
    let output_ty = ast_ty_to_ty(ccx, rb, decl.output);

    let t_fn = ty::mk_fn(ccx.tcx, {purity: purity,
                                   proto: ty::proto_bare,
                                   bounds: @~[],
                                   inputs: input_tys,
                                   output: output_ty,
                                   ret_style: ast::return_val});
    let tpt = {bounds: bounds, region_param: None, ty: t_fn};
    ccx.tcx.tcache.insert(def_id, tpt);
    return tpt;
}

fn mk_ty_params(ccx: @crate_ctxt, atps: ~[ast::ty_param])
    -> {bounds: @~[ty::param_bounds], params: ~[ty::t]} {

    let mut i = 0u;
    let bounds = ty_param_bounds(ccx, atps);
    {bounds: bounds,
     params: vec::map(atps, |atp| {
         let t = ty::mk_param(ccx.tcx, i, local_def(atp.id));
         i += 1u;
         t
     })}
}

fn mk_substs(ccx: @crate_ctxt, atps: ~[ast::ty_param],
             rp: Option<ty::region_variance>)
    -> {bounds: @~[ty::param_bounds], substs: ty::substs} {

    let {bounds, params} = mk_ty_params(ccx, atps);
    let self_r = rscope::bound_self_region(rp);
    {bounds: bounds, substs: {self_r: self_r, self_ty: None, tps: params}}
}
