use nano_lean::{Expr, Level};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use unbound::{Alpha, Name, Shared};
struct Meter;
static LIVE: AtomicUsize = AtomicUsize::new(0);
unsafe impl GlobalAlloc for Meter {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            LIVE.fetch_add(layout.size(), Relaxed);
        }
        ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Relaxed);
        unsafe {
            System.dealloc(ptr, layout);
        }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let out = unsafe { System.realloc(ptr, layout, size) };
        if !out.is_null() {
            LIVE.fetch_add(size, Relaxed);
            LIVE.fetch_sub(layout.size(), Relaxed);
        }
        out
    }
}
#[global_allocator]
static ALLOC: Meter = Meter;
fn measure(expr: Expr) -> usize {
    let mut terms = Vec::with_capacity(1000);
    let before = LIVE.load(Relaxed);
    for _ in 0..1000 {
        let term = Shared::new(expr.clone());
        drop(term.support());
        terms.push(term);
    }
    (LIVE.load(Relaxed) - before) / terms.len()
}
fn main() {
    let closed = measure(Expr::Sort(Level::Nat(0)));
    let bound = measure(Expr::Var(Name::bound(0, 0)));
    println!(
        "{{\"closed_node_requested_bytes\":{closed},\"one_bound_variable_node_requested_bytes\":{bound},\"samples_each\":1000,\"excludes\":\"vector slots, allocator overhead and payload allocations\"}}"
    );
}
