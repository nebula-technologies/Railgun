pub trait Merge<T, E> {
    fn merge<T1, U, F: FnOnce(T, T1) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        op: F,
    ) -> Result<U, E>;
    fn merge2<T1, T2, U, F: FnOnce(T, T1, T2) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        op: F,
    ) -> Result<U, E>;
    fn merge3<T1, T2, T3, U, F: FnOnce(T, T1, T2, T3) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        op: F,
    ) -> Result<U, E>;
    fn merge4<T1, T2, T3, T4, U, F: FnOnce(T, T1, T2, T3, T4) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        res4: Result<T4, E>,
        op: F,
    ) -> Result<U, E>;
}

impl<T, E> Merge<T, E> for Result<T, E> {
    fn merge<T1, U, F: FnOnce(T, T1) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        op: F,
    ) -> Result<U, E> {
        match (self, res1) {
            (Ok(t), Ok(t1)) => op(t, t1),
            (Err(e), Ok(_t1)) => Err(e),
            (Ok(_t), Err(e1)) => Err(e1),
            (Err(e), Err(_e1)) => Err(e),
        }
    }

    fn merge2<T1, T2, U, F: FnOnce(T, T1, T2) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        op: F,
    ) -> Result<U, E> {
        self.merge(res1, |t, t1| Ok(t).merge(res2, |t, t2| op(t, t1, t2)))
    }

    fn merge3<T1, T2, T3, U, F: FnOnce(T, T1, T2, T3) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        op: F,
    ) -> Result<U, E> {
        self.merge(res1, |t, t1| {
            Ok(t).merge(res2, |t, t2| Ok(t).merge(res3, |t, t3| op(t, t1, t2, t3)))
        })
    }

    fn merge4<T1, T2, T3, T4, U, F: FnOnce(T, T1, T2, T3, T4) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        res4: Result<T4, E>,
        op: F,
    ) -> Result<U, E> {
        self.merge(res1, |t, t1| {
            Ok(t).merge(res2, |t, t2| {
                Ok(t).merge(res3, |t, t3| {
                    Ok(t).merge(res4, |t, t4| op(t, t1, t2, t3, t4))
                })
            })
        })
    }
}
