use super::{Frame, Term, Thunk, Value, ValueData};
use crate::kernel::prelude::*;

// Iterative release so deep closure graphs do not overflow the stack on drop.
enum Edge {
    Term(Thunk),
    Frame(Rc<Frame>),
    Value(Value),
}
impl Term {
    fn detach(&mut self, pending: &mut Vec<Edge>) {
        pending.extend(self.context.take().map(Edge::Frame));
        for normal in &mut self.normal {
            if let Some(value) = normal.take() {
                pending.push(Edge::Value(value));
            }
        }
    }
}
impl Frame {
    pub(super) fn value(&self) -> &Thunk {
        self.value.as_ref().expect("live frame has a value")
    }
    fn detach(&mut self, pending: &mut Vec<Edge>) {
        pending.extend(self.value.take().map(Edge::Term));
        pending.extend(self.parent.take().map(Edge::Frame));
    }
}
fn release(mut pending: Vec<Edge>) {
    while let Some(edge) = pending.pop() {
        match edge {
            Edge::Term(term) => {
                if let Ok(mut term) = Rc::try_unwrap(term) {
                    term.detach(&mut pending);
                }
            }
            Edge::Frame(frame) => {
                if let Ok(mut frame) = Rc::try_unwrap(frame) {
                    frame.detach(&mut pending);
                }
            }
            Edge::Value(value) => {
                if let Ok(mut value) = Rc::try_unwrap(value) {
                    value.detach(&mut pending);
                }
            }
        }
    }
}
impl Drop for Term {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach(&mut pending);
        release(pending);
    }
}
impl Drop for Frame {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach(&mut pending);
        release(pending);
    }
}
impl ValueData {
    fn detach(&mut self, pending: &mut Vec<Edge>) {
        pending.extend(self.context.take().map(Edge::Frame));
        pending.extend(self.args.drain(..).map(Edge::Term));
    }
}
impl Drop for ValueData {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach(&mut pending);
        release(pending);
    }
}
