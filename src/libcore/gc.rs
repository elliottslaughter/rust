import stackwalk::Word;
import libc::size_t;
import libc::uintptr_t;
import send_map::linear::LinearMap;

export Word;
export gc;
export cleanup_stack_for_failure;

// Mirrors rust_stack.h stk_seg
struct StackSegment {
    let prev: *StackSegment;
    let next: *StackSegment;
    let end: uintptr_t;
    // And other fields which we don't care about...
}

extern mod rustrt {
    fn rust_annihilate_box(ptr: *Word);

    #[rust_stack]
    fn rust_call_tydesc_glue(root: *Word, tydesc: *Word, field: size_t);

    #[rust_stack]
    fn rust_gc_metadata() -> *Word;

    fn rust_get_stack_segment() -> *StackSegment;
}

unsafe fn is_frame_in_segment(fp: *Word, segment: *StackSegment) -> bool {
    let begin: Word = unsafe::reinterpret_cast(&segment);
    let end: Word = unsafe::reinterpret_cast(&(*segment).end);
    let frame: Word = unsafe::reinterpret_cast(&fp);

    return begin <= frame && frame <= end;
}

type SafePoint = { sp_meta: *Word, fn_meta: *Word };

unsafe fn debug_null_pc() {
    io::println("  is_safe_point: pc is null");
}

unsafe fn debug_safe_point_num(num: Word, sp_meta: *Word, fn_meta: *Word) {
    io::println(#fmt("  is_safe_point: selecting global safe point %u (at 0x%08x) in fn 0x%08x",
                     num,
                     unsafe::reinterpret_cast(&sp_meta),
                     unsafe::reinterpret_cast(&fn_meta)));
}

unsafe fn debug_no_safe_point(pc: *Word) {
    io::println(#fmt("  is_safe_point: no safe point for pc 0x%08x",
                     unsafe::reinterpret_cast(&pc)));
}

unsafe fn is_safe_point(pc: *Word) -> Option<SafePoint> {
    let module_meta = rustrt::rust_gc_metadata();
    let num_safe_points_ptr: *u32 = unsafe::reinterpret_cast(&module_meta);
    let num_safe_points = *num_safe_points_ptr as Word;
    let safe_points: *Word =
        ptr::offset(unsafe::reinterpret_cast(&module_meta), 1);

    if ptr::is_null(pc) {
        debug_null_pc();
        return None;
    }

    let mut sp = 0 as Word;
    while sp < num_safe_points {
        let sp_loc = *ptr::offset(safe_points, sp*3) as *Word;
        if sp_loc == pc {
            debug_safe_point_num(sp,
                                 *ptr::offset(safe_points, sp*3 + 1) as *Word,
                                 *ptr::offset(safe_points, sp*3 + 2) as *Word);
            return Some(
                {sp_meta: *ptr::offset(safe_points, sp*3 + 1) as *Word,
                 fn_meta: *ptr::offset(safe_points, sp*3 + 2) as *Word});
        }
        sp += 1;
    }
    debug_no_safe_point(pc);
    return None;
}

type Visitor = fn(root: **Word, tydesc: *Word) -> bool;

unsafe fn bump<T, U>(ptr: *T, count: uint) -> *U {
    return unsafe::reinterpret_cast(&ptr::offset(ptr, count));
}

unsafe fn align_to_pointer<T>(ptr: *T) -> *T {
    let align = sys::min_align_of::<*T>();
    let ptr: uint = unsafe::reinterpret_cast(&ptr);
    let ptr = (ptr + (align - 1)) & -align;
    return unsafe::reinterpret_cast(&ptr);
}

unsafe fn debug_stack(root: **Word, fp: *Word, offset: Word) {
    io::println(#fmt("  root 0x%08x (fp 0x%08x offset %d)",
                     unsafe::reinterpret_cast(&root),
                     unsafe::reinterpret_cast(&fp),
                     unsafe::reinterpret_cast(&offset)));
}

unsafe fn debug_safe_point_details(sp: SafePoint) {
    // Safe point internals
    let sp_meta: *u32 = unsafe::reinterpret_cast(&sp.sp_meta);

    let num_stack_roots: uint = *bump(sp_meta, 0);
    let num_reg_roots: uint = *bump(sp_meta, 1);
    let stack_roots: *u32 = bump(sp_meta, 2);
    let reg_roots: *u8 = bump(stack_roots, num_stack_roots);
    let addrspaces: *Word = align_to_pointer(bump(reg_roots, num_reg_roots));
    let _tydescs: ***Word = bump(addrspaces, num_stack_roots);

    // Function internals
    let fn_meta: *u32 = unsafe::reinterpret_cast(&sp.fn_meta);
    let num_callee_saved_regs: uint = *bump(fn_meta, 0);
    let num_safe_points: uint = *bump(fn_meta, 1);

    let callee_saved_offsets: *u32 = bump(fn_meta, 2);
    let callee_saved_regs: *u8 =
        bump(callee_saved_offsets, num_callee_saved_regs);

    let safe_points: *u32 =
        align_to_pointer(bump(callee_saved_regs, num_callee_saved_regs));
    let fn_name_start: *u32 = bump(safe_points, num_safe_points*2);
    let fn_name_len = *fn_name_start as uint;
    let fn_name =
        str::unsafe::from_buf_len(ptr::offset(fn_name_start, 1) as *u8,
                                  fn_name_len);

    io::println(#fmt("  details for safe point 0x%08x in fn %s",
                     unsafe::reinterpret_cast(&sp.sp_meta),
                     fn_name));
    io::println(#fmt("    in function with %u safe points, %u callee saved regs",
                     num_safe_points, num_callee_saved_regs));
    io::println(#fmt("    safe point has %u stack roots, %u reg roots",
                     num_stack_roots, num_reg_roots));

    // Stack roots
    let mut roots = ~[];
    let mut sri = 0;
    while sri < num_stack_roots {
        let offset = *ptr::offset(stack_roots, sri) as i32;
        vec::push(roots, offset);
        sri += 1;
    }
    let roots = roots;
    io::println(#fmt("      with stack roots %?", roots));
}

unsafe fn walk_safe_point(fp: *Word, sp: SafePoint, visitor: Visitor) {
    let fp_bytes: *u8 = unsafe::reinterpret_cast(&fp);
    let sp_meta_u32s: *u32 = unsafe::reinterpret_cast(&sp.sp_meta);

    let num_stack_roots = *sp_meta_u32s as uint;
    let num_reg_roots = *ptr::offset(sp_meta_u32s, 1) as uint;

    let stack_roots: *u32 =
        unsafe::reinterpret_cast(&ptr::offset(sp_meta_u32s, 2));
    let reg_roots: *u8 =
        unsafe::reinterpret_cast(&ptr::offset(stack_roots, num_stack_roots));
    let addrspaces: *Word =
        unsafe::reinterpret_cast(&ptr::offset(reg_roots, num_reg_roots));
    let tydescs: ***Word =
        unsafe::reinterpret_cast(&ptr::offset(addrspaces, num_stack_roots));

    // Stack roots
    let mut sri = 0;
    while sri < num_stack_roots {
        if *ptr::offset(addrspaces, sri) >= 1 {
            let root =
                ptr::offset(fp_bytes, *ptr::offset(stack_roots, sri) as Word)
                as **Word;
            debug_stack(root, fp, *ptr::offset(stack_roots, sri) as Word);
            let tydescpp = ptr::offset(tydescs, sri);
            let tydesc = if ptr::is_not_null(tydescpp) &&
                ptr::is_not_null(*tydescpp) {
                **tydescpp
            } else {
                ptr::null()
            };
            if !visitor(root, tydesc) { return; }
        }
        sri += 1;
    }

    // Register roots
    let mut rri = 0;
    while rri < num_reg_roots {
        if *ptr::offset(addrspaces, num_stack_roots + rri) == 1 {
            // FIXME(#2997): Need to find callee saved registers on the stack.
        }
        rri += 1;
    }
}

unsafe fn debug_frame(fp: *Word, pc: *Word, segment: *StackSegment, boundary: bool) {
    io::println(#fmt("stack frame: fp 0x%08x pc 0x%08x",
                     unsafe::reinterpret_cast(&fp),
                     unsafe::reinterpret_cast(&pc)));
    io::println(#fmt("  segment 0x%08x to 0x%08x (prev 0x%08x next 0x%08x)",
                     unsafe::reinterpret_cast(&segment),
                     unsafe::reinterpret_cast(&(*segment).end),
                     unsafe::reinterpret_cast(&(*segment).prev),
                     unsafe::reinterpret_cast(&(*segment).next)));
    if boundary {
        io::println("  at boundary: true");
    } else {
        io::println("  at boundary: false");
    }

/*
    io::println(#fmt("  stack contents at various offsets:"));
    io::println(#fmt("    fp-4: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, -4))));
    io::println(#fmt("    fp-3: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, -3))));
    io::println(#fmt("    fp-2: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, -2))));
    io::println(#fmt("    fp-1: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, -1))));
    io::println(#fmt("    fp+0: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 0))));
    io::println(#fmt("    fp+1: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 1))));
    io::println(#fmt("    fp+2: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 2))));
    io::println(#fmt("    fp+3: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 3))));
    io::println(#fmt("    fp+4: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 4))));
    io::println(#fmt("    fp+5: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 5))));
    io::println(#fmt("    fp+6: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 6))));
    io::println(#fmt("    fp+7: 0x%08x", unsafe::reinterpret_cast(&*ptr::offset(fp, 7))));
*/
}

unsafe fn debug_frame_not_in_segment(frame: *Word, segment: *StackSegment) {
    io::println(#fmt("  skipping: fp 0x%08x not in segment or prev segment",
                     unsafe::reinterpret_cast(&frame)));
    io::println(#fmt("    segment: start 0x%08x end 0x%08x",
                     unsafe::reinterpret_cast(&segment),
                     unsafe::reinterpret_cast(&(*segment).end)));
    if ptr::is_not_null((*segment).prev) {
        io::println(#fmt("    segment.prev: start 0x%08x end 0x%08x",
                         unsafe::reinterpret_cast(&(*segment).prev),
                         unsafe::reinterpret_cast(&(*(*segment).prev).end)));
    } else {
        io::println(#fmt("    segment.prev: is null"));
    }
    if ptr::is_not_null((*segment).next) {
        io::println(#fmt("    segment.next: start 0x%08x end 0x%08x",
                         unsafe::reinterpret_cast(&(*segment).next),
                         unsafe::reinterpret_cast(&(*(*segment).next).end)));
    } else {
        io::println(#fmt("    segment.next: is null"));
    }
}

unsafe fn debug_sentinel(root: **Word) {
    io::println(#fmt("    found sentinel: root 0x%08x",
                     unsafe::reinterpret_cast(&root)));
}

unsafe fn debug_not_yet_sentinel(root: **Word) {
    io::println(#fmt("    skipping (not yet sentinel): root 0x%08x",
                     unsafe::reinterpret_cast(&root)));
}

unsafe fn debug_skipping_null(root: **Word) {
    io::println(#fmt("    skipping null pointer: root 0x%08x",
                     unsafe::reinterpret_cast(&root)));
}

unsafe fn debug_root_value(root: **Word) {
    io::println(#fmt("    checking refcount: root 0x%08x box 0x%08x",
                    unsafe::reinterpret_cast(&root),
                    unsafe::reinterpret_cast(&*root)));
}

unsafe fn debug_never_reached_sentinel() {
    io::println("ERROR: never found sentinel!!!");
}

type Memory = uint;

const task_local_heap: Memory = 1;
const exchange_heap:   Memory = 2;
const stack:           Memory = 4;

const need_cleanup:    Memory = exchange_heap | stack;

unsafe fn find_segment_for_frame(fp: *Word, segment: *StackSegment)
    -> {segment: *StackSegment, boundary: bool} {
    // Check if frame is in either current frame or previous frame.
    let in_segment = is_frame_in_segment(fp, segment);
    let in_prev_segment = ptr::is_not_null((*segment).prev) &&
        is_frame_in_segment(fp, (*segment).prev);

    // If frame is not in either segment, walk down segment list until
    // we find the segment containing this frame.
    if !in_segment && !in_prev_segment {
        let mut segment = segment;
        while ptr::is_not_null((*segment).next) &&
            is_frame_in_segment(fp, (*segment).next) {
            segment = (*segment).next;
        }
        return {segment: segment, boundary: false};
    }

    // If frame is in previous frame, then we're at a boundary.
    if !in_segment && in_prev_segment {
        return {segment: (*segment).prev, boundary: true};
    }

    // Otherwise, we're somewhere on the inside of the frame.
    return {segment: segment, boundary: false};
}

unsafe fn walk_gc_roots(mem: Memory, sentinel: **Word, visitor: Visitor) {
    let mut segment = rustrt::rust_get_stack_segment();
    let mut last_ret: *Word = ptr::null();
    // To avoid collecting memory used by the GC itself, skip stack
    // frames until past the root GC stack frame. The root GC stack
    // frame is marked by a sentinel, which is a box pointer stored on
    // the stack.
    let mut reached_sentinel = ptr::is_null(sentinel);
    for stackwalk::walk_stack |frame| {
        unsafe {
            let pc = last_ret;
            let {segment: next_segment, boundary: boundary} =
                find_segment_for_frame(frame.fp, segment);
            segment = next_segment;
            debug_frame(frame.fp, pc, segment, boundary);
            let ret_offset = if boundary { 4 } else { 1 };
            last_ret = *ptr::offset(frame.fp, ret_offset) as *Word;

            if ptr::is_null(pc) {
                again;
            }

            let mut delay_reached_sentinel = reached_sentinel;
            let sp = is_safe_point(pc);
            match sp {
              Some(sp_info) => {
                debug_safe_point_details(sp_info);
                for walk_safe_point(frame.fp, sp_info) |root, tydesc| {
                    // Skip roots until we see the sentinel.
                    if !reached_sentinel {
                        if root == sentinel { 
                            debug_sentinel(root);
                            delay_reached_sentinel = true;
                        } else {
                            debug_not_yet_sentinel(root);
                        }
                        again;
                    }

                    // Skip null pointers, which can occur when a
                    // unique pointer has already been freed.
                    if ptr::is_null(*root) {
                        debug_skipping_null(root);
                        again;
                    }

                    debug_root_value(root);
                    if ptr::is_null(tydesc) {
                        // Root is a generic box.
                        let refcount = **root;
                        if mem | task_local_heap != 0 && refcount != -1 {
                            if !visitor(root, tydesc) { return; }
                        } else if mem | exchange_heap != 0 && refcount == -1 {
                            if !visitor(root, tydesc) { return; }
                        }
                    } else {
                        // Root is a non-immediate.
                        if mem | stack != 0 {
                            if !visitor(root, tydesc) { return; }
                        }
                    }
                }
              }
              None => ()
            }
            reached_sentinel = delay_reached_sentinel;
        }
    }
    if reached_sentinel == false {
        debug_never_reached_sentinel();
    }
}

fn gc() {
    unsafe {
        for walk_gc_roots(task_local_heap, ptr::null()) |_root, _tydesc| {
            // FIXME(#2997): Walk roots and mark them.
            io::stdout().write([46]); // .
        }
    }
}

type RootSet = LinearMap<*Word,()>;

fn RootSet() -> RootSet {
    LinearMap()
}

// Debug wrappers to allow printing.
unsafe fn annihilate(root: **Word) {
    io::println(#fmt("      rust_annihilate_box: root 0x%08x box 0x%08x",
                     unsafe::reinterpret_cast(&root),
                     unsafe::reinterpret_cast(&*root)));
    rustrt::rust_annihilate_box(*root);
}

unsafe fn call_glue(root: **Word, tydesc: *Word, field: size_t) {
    io::println(#fmt("      rust_annihilate_box: root 0x%08x box 0x%08x",
                     unsafe::reinterpret_cast(&root),
                     unsafe::reinterpret_cast(&*root)));
    rustrt::rust_call_tydesc_glue(*root, tydesc, field);
}

unsafe fn debug_init_sentinel(root: **Word) {
    io::println(#fmt("sentinel: 0x%08x",
                    unsafe::reinterpret_cast(&root)));
}

unsafe fn debug_rootset(root: **Word, box: *Word) {
    io::println(#fmt("rootset: root 0x%08x box 0x%08x",
                     unsafe::reinterpret_cast(&root),
                     unsafe::reinterpret_cast(&box)));
}

#[cfg(gc)]
fn expect_sentinel() -> bool { true }

#[cfg(nogc)]
fn expect_sentinel() -> bool { false }

// This should only be called from fail, as it will drop the roots
// which are *live* on the stack, rather than dropping those that are
// dead.
fn cleanup_stack_for_failure() {
    unsafe {
        // Leave a sentinel on the stack to mark the current frame. The
        // stack walker will ignore any frames above the sentinel, thus
        // avoiding collecting any memory being used by the stack walker
        // itself.
        //
        // However, when core itself is not compiled with GC, then none of
        // the functions in core will have GC metadata, which means we
        // won't be able to find the sentinel root on the stack. In this
        // case, we can safely skip the sentinel since we won't find our
        // own stack roots on the stack anyway.
        let sentinel_box = ~0;
        let sentinel: **Word = if expect_sentinel() {
            unsafe::reinterpret_cast(&ptr::addr_of(sentinel_box))
        } else {
            ptr::null()
        };

        let mut roots = ~RootSet();
        debug_init_sentinel(sentinel);
        debug_rootset(unsafe::reinterpret_cast(&ptr::addr_of(roots)),
                      unsafe::reinterpret_cast(&roots));
        for walk_gc_roots(need_cleanup, sentinel) |root, tydesc| {
            // Track roots to avoid double frees.
            if option::is_some(roots.find(&*root)) {
                again;
            }
            roots.insert(*root, ());

            if ptr::is_null(tydesc) {
                //rustrt::rust_annihilate_box(*root);
                annihilate(root);
            } else {
                //rustrt::rust_call_tydesc_glue(*root, tydesc, 3 as size_t);
                call_glue(root, tydesc, 3 as size_t);
            }
        }
    }
}
