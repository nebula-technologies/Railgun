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
    ///
    /// ```
    /// use railsgun::Merge;
    ///
    /// fn func_xyz(v: u32, w: u32) -> Result<u32,u32> {
    ///     Ok( v + w)
    /// }
    ///
    /// let v = Ok(1);
    /// let w = Ok(2);
    /// v.merge(w, |var_v, var_w| func_xyz(var_v, var_w)).ok();
    /// ```
    #[inline]
    fn merge<T1, U, F: FnOnce(T, T1) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        op: F,
    ) -> Result<U, E> {
        match (self, res1) {
            (Ok(t), Ok(t1)) => op(t, t1),
            (Err(e), _) => Err(e),
            (_, Err(e1)) => Err(e1),
        }
    }

    ///
    /// ```
    /// use railsgun::Merge;
    ///
    /// fn func_xyz(v: u32, w: u32, x: u32) -> Result<u32,u32> {
    ///     Ok( v + w + x )
    /// }
    ///
    /// let v = Ok(1);
    /// let w = Ok(2);
    /// let x = Ok(2);
    /// v.merge2(w, x, |var_v, var_w, var_x| func_xyz(var_v, var_w, var_x)).ok();
    /// ```
    #[inline]
    fn merge2<T1, T2, U, F: FnOnce(T, T1, T2) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        op: F,
    ) -> Result<U, E> {
        match (self, res1, res2) {
            (Ok(t), Ok(t1), Ok(t2)) => op(t, t1, t2),
            (Err(e), _, _) => Err(e),
            (_, Err(e), _) => Err(e),
            (_, _, Err(e)) => Err(e),
        }
    }

    ///
    /// ```
    /// use railsgun::Merge;
    ///
    /// fn func_xyz(v: u32, w: u32, x: u32, y: u32) -> Result<u32,u32> {
    ///     Ok( v + w + x + y)
    /// }
    ///
    /// let v = Ok(1);
    /// let w = Ok(2);
    /// let x = Ok(2);
    /// let y = Ok(2);
    /// v.merge3(w, x, y, |var_v, var_w, var_x, var_y| func_xyz(var_v, var_w, var_x, var_y)).ok();
    /// ```
    #[inline]
    fn merge3<T1, T2, T3, U, F: FnOnce(T, T1, T2, T3) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        op: F,
    ) -> Result<U, E> {
        match (self, res1, res2, res3) {
            (Ok(t), Ok(t1), Ok(t2), Ok(t3)) => op(t, t1, t2, t3),
            (Err(e), _, _, _) => Err(e),
            (_, Err(e), _,_) => Err(e),
            (_, _, Err(e),_) => Err(e),
            (_, _,_,Err(e)) => Err(e),
        }
    }

    ///
    /// ```
    /// use railsgun::Merge;
    ///
    /// fn func_xyz(v: u32, w: u32, x: u32, y: u32, z: u32) -> Result<u32,u32> {
    ///     Ok( v + w + x + y + z)
    /// }
    ///
    /// let v = Ok(1);
    /// let w = Ok(2);
    /// let x = Ok(2);
    /// let y = Ok(2);
    /// let z = Ok(2);
    /// v.merge4(w, x, y, z, |var_v, var_w, var_x, var_y, var_z| func_xyz(var_v, var_w, var_x, var_y, var_z)).ok();
    /// ```
    #[inline]
    fn merge4<T1, T2, T3, T4, U, F: FnOnce(T, T1, T2, T3, T4) -> Result<U, E>>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        res4: Result<T4, E>,
        op: F,
    ) -> Result<U, E> {
        match (self, res1, res2, res3, res4) {
            (Ok(t), Ok(t1), Ok(t2), Ok(t3), Ok(t4)) => op(t, t1, t2, t3, t4),
            (Err(e), _, _, _,_) => Err(e),
            (_, Err(e), _,_,_) => Err(e),
            (_, _, Err(e),_,_) => Err(e),
            (_, _,_,Err(e),_) => Err(e),
            (_, _,_,_,Err(e)) => Err(e),
        }
    }
}


pub trait MergeOption<T> {
    fn merge<T1, U, F: FnOnce(T, T1) -> Option<U>>(
        self,
        res1: Option<T1>,
        op: F,
    ) -> Option<U>;
    fn merge2<T1, T2, U, F: FnOnce(T, T1, T2) -> Option<U>>(
        self,
        res1: Option<T1>,
        res2: Option<T2>,
        op: F,
    ) -> Option<U>;
    fn merge3<T1, T2, T3, U, F: FnOnce(T, T1, T2, T3) -> Option<U>>(
        self,
        res1: Option<T1>,
        res2: Option<T2>,
        res3: Option<T3>,
        op: F,
    ) -> Option<U>;
    fn merge4<T1, T2, T3, T4, U, F: FnOnce(T, T1, T2, T3, T4) -> Option<U>>(
        self,
        res1: Option<T1>,
        res2: Option<T2>,
        res3: Option<T3>,
        res4: Option<T4>,
        op: F,
    ) -> Option<U>;
}

impl<T> MergeOption<T> for Option<T> {
    ///
    /// ```
    /// use railsgun::MergeOption;
    ///
    /// fn func_xyz(v: u32, w: u32) -> Option<u32> {
    ///     Some( v + w)
    /// }
    ///
    /// let v = Some(1);
    /// let w = Some(2);
    /// v.merge(w, |var_v, var_w| func_xyz(var_v, var_w));
    /// ```
    #[inline]
    fn merge<T1, U, F: FnOnce(T, T1) -> Option<U>>(
        self,
        res1: Option<T1>,
        op: F,
    ) -> Option<U> {
        match (self, res1) {
            (Some(t), Some(t1)) => op(t, t1),
            _ => None
        }
    }

    ///
    /// ```
    /// use railsgun::MergeOption;
    ///
    /// fn func_xyz(v: u32, w: u32, x: u32) -> Option<u32> {
    ///     Some( v + w + x )
    /// }
    ///
    /// let v = Some(1);
    /// let w = Some(2);
    /// let x = Some(2);
    /// v.merge2(w, x, |var_v, var_w, var_x| func_xyz(var_v, var_w, var_x));
    /// ```
    #[inline]
    fn merge2<T1, T2, U, F: FnOnce(T, T1, T2) -> Option<U>>(
        self,
        res1: Option<T1>,
        res2: Option<T2>,
        op: F,
    ) -> Option<U> {

        match (self, res1, res2) {
            (Some(t),Some(t1), Some(t2)) => op(t, t1, t2),
            _ => None
        }
    }

    ///
    /// ```
    /// use railsgun::MergeOption;
    ///
    /// fn func_xyz(v: u32, w: u32, x: u32, y: u32) -> Option<u32> {
    ///     Some( v + w + x + y)
    /// }
    ///
    /// let v = Some(1);
    /// let w = Some(2);
    /// let x = Some(2);
    /// let y = Some(2);
    /// v.merge3(w, x, y, |var_v, var_w, var_x, var_y| func_xyz(var_v, var_w, var_x, var_y));
    /// ```
    #[inline]
    fn merge3<T1, T2, T3, U, F: FnOnce(T, T1, T2, T3) -> Option<U>>(
        self,
        res1: Option<T1>,
        res2: Option<T2>,
        res3: Option<T3>,
        op: F,
    ) -> Option<U> {
        match (self, res1, res2, res3) {
            (Some(t),Some(t1), Some(t2), Some(t3)) => op(t, t1, t2, t3),
            _ => None
        }
    }

    ///
    /// ```
    /// use railsgun::MergeOption;
    ///
    /// fn func_xyz(v: u32, w: u32, x: u32, y: u32, z: u32) -> Option<u32> {
    ///     Some( v + w + x + y + z)
    /// }
    ///
    /// let v = Some(1);
    /// let w = Some(2);
    /// let x = Some(2);
    /// let y = Some(2);
    /// let z = Some(2);
    /// v.merge4(w, x, y, z, |var_v, var_w, var_x, var_y, var_z| func_xyz(var_v, var_w, var_x, var_y, var_z));
    /// ```
    #[inline]
    fn merge4<T1, T2, T3, T4, U, F: FnOnce(T, T1, T2, T3, T4) -> Option<U>>(
        self,
        res1: Option<T1>,
        res2: Option<T2>,
        res3: Option<T3>,
        res4: Option<T4>,
        op: F,
    ) -> Option<U> {
        match (self, res1, res2, res3, res4) {
            (Some(t),Some(t1), Some(t2), Some(t3), Some(t4)) => op(t, t1, t2, t3, t4),
            _ => None
        }
    }
}
#[cfg(test)]
mod test {
    use crate::Merge;

    #[tokio::test]
    async fn test_merge() {
        fn func_xyz(v: u32, w: u32) -> Result<u32, u32> {
            Ok(v + w)
        }

        let v = Ok(1);
        let w = Ok(2);
        v.merge(w, |var_v, var_w| func_xyz(var_v, var_w)).ok();
    }

    #[tokio::test]
    async fn test_merge2() {
        fn func_xyz(v: u32, w: u32, x: u32) -> Result<u32, u32> {
            Ok(v + w + x)
        }

        let v = Ok(1);
        let w = Ok(2);
        let x = Ok(2);
        v.merge2(w, x, |var_v, var_w, var_x| func_xyz(var_v, var_w, var_x))
            .ok();
    }

    #[tokio::test]
    async fn test_merge3() {
        fn func_xyz(v: u32, w: u32, x: u32, y: u32) -> Result<u32, u32> {
            Ok(v + w + x + y)
        }

        let v = Ok(1);
        let w = Ok(2);
        let x = Ok(2);
        let y = Ok(2);
        v.merge3(w, x, y, |var_v, var_w, var_x, var_y| {
            func_xyz(var_v, var_w, var_x, var_y)
        })
        .ok();
    }

    #[tokio::test]
    async fn test_merge4() {
        fn func_xyz(v: u32, w: u32, x: u32, y: u32, z: u32) -> Result<u32, u32> {
            Ok(v + w + x + y + z)
        }

        let v = Ok(1);
        let w = Ok(2);
        let x = Ok(2);
        let y = Ok(2);
        let z = Ok(2);
        v.merge4(w, x, y, z, |var_v, var_w, var_x, var_y, var_z| {
            func_xyz(var_v, var_w, var_x, var_y, var_z)
        })
        .ok();
    }
}
