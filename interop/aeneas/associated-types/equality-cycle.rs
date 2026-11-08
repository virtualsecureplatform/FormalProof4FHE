pub trait Field: Sized {
    type Plan: Table<Self>;
    type Root;
    fn from_root(root: Self::Root) -> Self;
}
pub trait Table<F: Field<Plan = Self>>: Sized {
    fn root(&self) -> F;
}
pub fn convert<F: Field>(root: F::Root) -> F {
    F::from_root(root)
}
