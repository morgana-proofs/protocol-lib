#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SumClaim<F>(pub F);

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct EvalClaim<F> {
    pub ev: F,
    pub point: Vec<F>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SinglePointClaims<F> {
    pub evs: Vec<F>,
    pub point: Vec<F>,
}