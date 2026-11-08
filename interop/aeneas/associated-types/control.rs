pub trait Field: Sized {
    type Root;
    fn from_root(root: Self::Root) -> Self;
}
pub fn convert<F: Field>(root: F::Root) -> F {
    F::from_root(root)
}
pub fn constrained<F: Field<Root = u64>>(root: u64) -> F {
    F::from_root(root)
}
pub fn chain<F: Field, G: Field<Root = F>>(root: F::Root) -> G {
    G::from_root(F::from_root(root))
}
