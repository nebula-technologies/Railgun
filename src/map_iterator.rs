pub trait ResultMapIterator<T, E> {
    fn iter_map<U, F: Fn(T) -> Result<U, E>>(self, op: F) -> Result<Vec<U>, E>;
}

impl<T: Clone, E> ResultMapIterator<T, E> for Result<Vec<T>, E> {
    fn iter_map<U, F: Fn(T) -> Result<U, E>>(self, op: F) -> Result<Vec<U>, E> {
        match self {
            Ok(vt) => vt.into_iter().map(|t| op(t)).collect(),
            Err(e) => Err(e),
        }
    }
}
