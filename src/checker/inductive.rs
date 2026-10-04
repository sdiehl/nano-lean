use super::Tc;
use crate::ensure;
use crate::term::decl::Declar;

impl<'t, 'a: 't> Tc<'t, 'a> {
    /// Check signatures in dependency order within exactly one imported block.
    /// Full positivity and generated-recursor validation remain separate work.
    pub(crate) fn check_inductive(&mut self, idx: u32, d: Declar<'t>) {
        let block = *self
            .ctx
            .store
            .blocks
            .get(&d.name())
            .expect("imported inductive block");
        if block.start != idx {
            return;
        }
        for position in block.start..block.end {
            let d = self.ctx.store.declars[position as usize];
            self.uparams = d.uparams();
            self.limit = if position < block.types_end {
                block.start
            } else if position < block.ctors_end {
                block.types_end
            } else {
                block.ctors_end
            };
            ensure!(self.limit <= position, "invalid inductive dependency order");
            self.check_type(d.ty());
        }
    }
}
