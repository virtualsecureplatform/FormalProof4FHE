pub fn phantom_clone<T>(value: &core::marker::PhantomData<T>) -> core::marker::PhantomData<T> {
    value.clone()
}
