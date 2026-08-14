//! Shadow storage shell. Authoritative family data moves here only in SS2--SS5.

#[derive(Debug, Default)]
pub(super) struct ProofRelations {
    shadow_publications: u64,
}

#[derive(Debug, Default)]
pub(super) struct BoundRelations {
    shadow_publications: u64,
}

#[derive(Debug, Default)]
pub(super) struct ConstraintRelations {
    shadow_publications: u64,
}

#[derive(Debug, Default)]
pub(super) struct RowRelations {
    shadow_publications: u64,
}

#[derive(Debug, Default)]
pub(super) struct IdentityRelations {
    shadow_publications: u64,
}

#[derive(Debug, Default)]
pub(in crate::constraints::structural_kernel) struct StructuralData {
    proof: ProofRelations,
    bounds: BoundRelations,
    constraints: ConstraintRelations,
    rows: RowRelations,
    identities: IdentityRelations,
}

impl StructuralData {
    pub(super) fn record_proof_shadow(&mut self) {
        self.proof.shadow_publications = self.proof.shadow_publications.saturating_add(1);
    }

    pub(super) fn record_bounds_shadow(&mut self) {
        self.bounds.shadow_publications = self.bounds.shadow_publications.saturating_add(1);
    }

    pub(super) fn record_constraints_shadow(&mut self) {
        self.constraints.shadow_publications =
            self.constraints.shadow_publications.saturating_add(1);
    }

    pub(super) fn record_rows_shadow(&mut self) {
        self.rows.shadow_publications = self.rows.shadow_publications.saturating_add(1);
    }

    pub(super) fn record_identities_shadow(&mut self) {
        self.identities.shadow_publications = self.identities.shadow_publications.saturating_add(1);
    }

    #[cfg(test)]
    pub(super) fn shadow_publication_counts(&self) -> [u64; 5] {
        [
            self.proof.shadow_publications,
            self.bounds.shadow_publications,
            self.constraints.shadow_publications,
            self.rows.shadow_publications,
            self.identities.shadow_publications,
        ]
    }

    #[cfg(cpk_sv_d_ss1_rf_ui_raw_escape)]
    pub(in crate::constraints::structural_kernel) fn raw_shadow_probe(&self) -> &u64 {
        &self.proof.shadow_publications
    }
}
