pub struct SumClaim<F>(pub F);

pub struct EvalClaim<F> {
    pub ev: F,
    pub point: Vec<F>,
}

#[derive(Clone)]
pub struct SinglePointClaims<F> {
    pub evs: Vec<F>,
    pub point: Vec<F>,
}