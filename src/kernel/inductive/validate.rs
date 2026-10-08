use super::*;

impl Environment {
    pub(super) fn validate_inductive_export(
        &self,
        actual: &InductiveBlock,
        expected: &InductiveBlock,
    ) -> Result<()> {
        demand(
            actual.types.len() == expected.types.len()
                && actual.constructors.len() == expected.constructors.len(),
            "incorrect inductive declaration count",
        )?;
        demand(
            actual.recursors.len() == expected.recursors.len(),
            "incorrect recursor count",
        )?;
        for (a, e) in actual.types.iter().zip(&expected.types) {
            demand(
                a.name == e.name
                    && a.params == e.params
                    && a.all == e.all
                    && a.constructors == e.constructors
                    && a.num_params == e.num_params
                    && a.num_indices == e.num_indices
                    && a.num_nested == e.num_nested,
                "incorrect inductive metadata",
            )?;
            demand(
                a.recursive == e.recursive && a.reflexive == e.reflexive,
                "incorrect inductive recursion metadata",
            )?;
        }
        for e in &expected.constructors {
            let a = actual
                .constructors
                .iter()
                .find(|c| c.name == e.name)
                .ok_or_else(|| Error::Rejected("missing constructor".into()))?;
            let mut tc = self.checker(&e.params);
            tc.sort(&a.ty)?;
            demand(tc.conv(&a.ty, &e.ty)?, "incorrect constructor type")?;
        }
        for e in &expected.recursors {
            let a = actual
                .recursors
                .iter()
                .find(|r| r.name == e.name)
                .ok_or_else(|| Error::Rejected("missing recursor".into()))?;
            self.validate_recursor(a, e, &expected.types[0].params)?;
        }
        Ok(())
    }

    fn validate_recursor(&self, a: &Recursor, e: &Recursor, type_params: &[String]) -> Result<()> {
        demand(
            a.all == e.all
                && a.num_params == e.num_params
                && a.num_indices == e.num_indices
                && a.num_motives == e.num_motives
                && a.num_minors == e.num_minors
                && a.k == e.k,
            "incorrect recursor metadata",
        )?;
        if e.params.len() == type_params.len() {
            demand(
                a.params == type_params,
                "invalid large elimination from proposition",
            )?;
        } else {
            demand(
                Recursor::large_params(&a.params, type_params),
                "incorrect recursor universe parameters",
            )?;
        }
        let levels: BTreeMap<_, _> = a
            .params
            .iter()
            .cloned()
            .zip(e.params.iter().cloned().map(Level::Param))
            .collect();
        let mut tc = self.checker(&e.params);
        let ty = a.ty.substitute_levels(&levels)?;
        tc.sort(&e.ty)?;
        tc.sort(&ty)?;
        demand(tc.conv(&ty, &e.ty)?, "incorrect recursor type")?;
        demand(
            a.rules.len() == e.rules.len(),
            "incorrect recursor rule count",
        )?;
        for (ar, er) in a.rules.iter().zip(&e.rules) {
            demand(
                ar.constructor == er.constructor && ar.num_fields == er.num_fields,
                "incorrect recursor rule metadata",
            )?;
            let rhs = ar.rhs.substitute_levels(&levels)?;
            let ty = tc.infer(&er.rhs)?;
            tc.check(&rhs, &ty)?;
            demand(
                tc.conv(&rhs, &er.rhs)?,
                "incorrect recursor computation rule",
            )?;
        }
        Ok(())
    }
}
