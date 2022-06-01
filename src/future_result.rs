use core::pin::Pin;
use std::future::Future;

pub trait FutureResult<T, E> {
    fn map<'a, U, F, TU>(self, op: F) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> TU + Send,
        TU: Future<Output = U> + Send;

    fn map_or<'a, U, UO, F>(self, default: U, f: F) -> Pin<Box<dyn Future<Output = U> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> UO + Send,
        UO: Future<Output = U> + Send,
        U: 'a + Send;

    fn map_err<'a, F, UO, O>(
        self,
        op: O,
    ) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> UO + Send,
        UO: Future<Output = F> + Send;

    fn and_then<'a, U, F, FO>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> FO + Send,
        FO: Future<Output = Result<U, E>> + Send;

    fn or_else<'a, F, EO, O>(
        self,
        op: O,
    ) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> EO + Send,
        EO: Future<Output = Result<T, F>> + Send;

    fn unwrap_or_else<'a, TO, F>(self, op: F) -> Pin<Box<dyn Future<Output = T> + Send + 'a>>
    where
        Self: 'a,
        TO: Future<Output = T> + Send,
        F: 'a + FnOnce(E) -> TO + Send;

    fn merge<'a, T1, U, FO, F>(
        self,
        res1: Result<T1, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1) -> FO + Send,
        T1: 'a + Send;

    fn merge2<'a, T1, T2, U, FO, F>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1, T2) -> FO + Send,
        T1: 'a + Send,
        T2: 'a + Send;

    fn merge3<'a, T1, T2, T3, U, FO, F>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1, T2, T3) -> FO + Send,
        T1: 'a + Send,
        T2: 'a + Send,
        T3: 'a + Send;

    fn merge4<'a, T1, T2, T3, T4, U, FO, F>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        res4: Result<T4, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1, T2, T3, T4) -> FO + Send,
        T1: 'a + Send,
        T2: 'a + Send,
        T3: 'a + Send,
        T4: 'a + Send;
}

impl<T: Send, E: Send, L> FutureResult<T, E> for L
where
    L: Future<Output = Result<T, E>> + Send,
{
    /// Maps a `Result<T, E>` to `Result<U, E>` by applying a function to a
    /// contained [`Ok`] value, leaving an [`Err`] value untouched.
    ///
    /// This function can be used to compose the results of two functions.
    ///
    /// # Examples
    ///
    /// Print the numbers on each line of a string multiplied by two.
    ///
    /// ```
    /// use railsgun::FutureResult;
    /// async fn function() -> Result<String, String> {
    ///    Ok("foo".to_string())
    /// }
    ///
    /// # async fn run() -> () {
    /// function()
    ///     .map(|t| async move { format!("Magic: {}", t) })
    ///     .map(|t| async move { println!("{}", t) })
    ///     .await
    ///     .ok();
    /// # }
    /// ```
    #[inline]
    fn map<'a, U, F, TU>(self, op: F) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + (FnOnce(T) -> TU) + Send,
        TU: Future<Output = U> + Send,
    {
        Box::pin(async move {
            match self.await {
                Ok(t) => Ok(op(t).await),
                Err(e) => Err(e),
            }
        })
    }

    /// Applies a function to the contained value (if [`Ok`]),
    /// or returns the provided default (if [`Err`]).
    ///
    /// Arguments passed to `map_or` are eagerly evaluated; if you are passing
    /// the Result of a function call, it is recommended to use [`map_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`map_or_else`]: Result::map_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::future::Future;
    /// use railsgun::FutureResult;
    ///
    ///  async fn run() -> () {
    /// let x = async {Ok("foo") as Result<&str, &str>};
    /// assert_eq!(x.map_or(42, |v| async move {v.len()}).await, 3);
    ///
    /// let x = async{Err("bar") as Result<&str, &str>};
    /// assert_eq!(x.map_or(42, |v| async move {v.len()}).await, 42);
    /// # }
    /// ```
    #[inline]
    fn map_or<'a, U, UO, F>(self, default: U, f: F) -> Pin<Box<dyn Future<Output = U> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> UO + Send,
        UO: Future<Output = U> + Send,
        U: 'a + Send,
    {
        Box::pin(async {
            match self.await {
                Ok(t) => f(t).await,
                Err(_) => default,
            }
        })
    }

    /// Maps a `Result<T, E>` to `Result<T, F>` by applying a function to a
    /// contained [`Err`] value, leaving an [`Ok`] value untouched.
    ///
    /// This function can be used to pass through a successful Result while handling
    /// an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use std::future::Future;
    /// use railsgun::FutureResult;
    /// async fn stringify(x: i32) -> String{ format!("error code: {}", x) }
    ///
    /// # async fn run() -> () {
    /// let x = async {Ok(2) as Result<i32, i32>};
    /// assert_eq!(x.map_err(stringify).await, Ok(2));
    ///
    /// let x = async {Err(13) as Result<i32, i32>};
    /// assert_eq!(x.map_err(stringify).await, Err("error code: 13".to_string()));
    /// # }
    /// ```
    #[inline]
    fn map_err<'a, F, UO, O>(self, op: O) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> UO + Send,
        UO: Future<Output = F> + Send,
    {
        Box::pin(async move {
            match self.await {
                Ok(t) => Ok(t),
                Err(e) => Err(op(e).await),
            }
        })
    }

    /// Calls `op` if the Result is [`Ok`], otherwise returns the [`Err`] value of `self`.
    ///
    ///
    /// This function can be used for control flow based on `Result` values.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use std::future::Future;
    /// use railsgun::FutureResult;
    ///
    /// # async fn run() -> () {
    ///
    /// async fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
    /// async fn err(x: u32) -> Result<u32, u32> { Err(x) }
    ///
    /// assert_eq!(async{Ok(2)}.and_then(sq).and_then(sq).await, Ok(16));
    /// assert_eq!(async{Ok(2)}.and_then(sq).and_then(err).await, Err(4));
    /// assert_eq!(async{Ok(2)}.and_then(err).and_then(sq).await, Err(2));
    /// assert_eq!(async{Err(3)}.and_then(sq).and_then(sq).await, Err(3));
    /// # }
    /// ```
    #[inline]
    fn and_then<'a, U, F, FO>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> FO + Send,
        FO: Future<Output = Result<U, E>> + Send,
    {
        Box::pin(async move {
            match self.await {
                Ok(t) => op(t).await,
                Err(e) => Err(e),
            }
        })
    }
    /// Calls `op` if the Result is [`Err`], otherwise returns the [`Ok`] value of `self`.
    ///
    /// This function can be used for control flow based on Result values.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railsgun::FutureResult;
    ///
    /// async fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
    /// async fn err(x: u32) -> Result<u32, u32> { Err(x) }
    ///
    /// # async fn run() -> () {
    /// assert_eq!(async{Ok(2)}.or_else(sq).or_else(sq).await, Ok(2));
    /// assert_eq!(async{Ok(2)}.or_else(err).or_else(sq).await, Ok(2));
    /// assert_eq!(async{Err(3)}.or_else(sq).or_else(err).await, Ok(9));
    /// assert_eq!(async{Err(3)}.or_else(err).or_else(err).await, Err(3));
    /// # }
    /// ```
    #[inline]
    fn or_else<'a, F, EO, O>(self, op: O) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> EO + Send,
        EO: Future<Output = Result<T, F>> + Send,
    {
        Box::pin(async move {
            match self.await {
                Ok(t) => Ok(t),
                Err(e) => op(e).await,
            }
        })
    }
    /// Returns the contained [`Ok`] value or computes it from a closure.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railsgun::FutureResult;
    ///
    /// async fn count(x: &str) -> usize { x.len() }
    ///
    /// # async fn run() -> () {
    /// assert_eq!(async{Ok(2)}.unwrap_or_else(count).await, 2);
    /// assert_eq!(async{Err("foo")}.unwrap_or_else(count).await, 3);
    /// # }
    /// ```
    #[inline]
    fn unwrap_or_else<'a, TO, F>(self, op: F) -> Pin<Box<dyn Future<Output = T> + Send + 'a>>
    where
        Self: 'a,
        TO: Future<Output = T> + Send,
        F: 'a + FnOnce(E) -> TO + Send,
    {
        Box::pin(async move {
            match self.await {
                Ok(t) => t,
                Err(e) => op(e).await,
            }
        })
    }

    /// ```
    /// use railsgun::FutureResult;
    ///
    /// # async fn run() {
    /// fn func_xyz(x: u32, y: u32) -> Result<u32,u32> {
    ///     Ok( x + y)
    /// }
    ///
    /// let x = async {Ok(1u32) as Result<u32, u32>};
    /// let x1 = async {Ok(1u32) as Result<u32, u32>};
    /// let xe = async {Ok(4u32) as Result<u32, u32>};
    /// let y = Ok(2);
    /// let ye = Err(3);
    ///
    /// assert_eq!(x.merge(y, |var_x, var_y,| async move {func_xyz(var_x, var_y)})
    ///     .await
    ///     .unwrap(), 3u32);
    ///
    /// assert_eq!(xe.merge(y, |var_x, var_y,| async move {func_xyz(var_x, var_y)})
    ///     .await
    ///     .unwrap_err(), 4u32);
    ///
    /// assert_eq!(x1.merge(ye, |var_x, var_y,| async move {func_xyz(var_x, var_y)})
    ///     .await
    ///     .unwrap(), 5u32);
    ///
    /// # }
    /// ```
    #[inline]
    fn merge<'a, T1, U, FO, F>(
        self,
        res1: Result<T1, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1) -> FO + Send,
        T1: 'a + Send,
    {
        Box::pin(async move {
            match (self.await, res1) {
                (Ok(t), Ok(t1)) => op(t, t1).await,
                (Err(e), _) => Err(e),
                (_, Err(e1)) => Err(e1),
            }
        })
    }

    ///
    /// ```
    /// use railsgun::FutureResult;
    ///
    /// # async fn run() {
    /// fn func_xyz(v: u32, w: u32, x: u32) -> Result<u32,u32> {
    ///     Ok( v + w + x )
    /// }
    ///
    /// let v = async {Ok(1u32) as Result<u32, u32>};
    /// let w = Ok(2);
    /// let x = Ok(2);
    /// assert_eq!(v
    ///     .merge2(w, x,
    ///         |var_v, var_w, var_x|
    ///         async move {func_xyz(var_v, var_w, var_x)}
    ///     )
    ///     .await.unwrap(), 5u32);
    /// # }
    /// ```
    #[inline]
    fn merge2<'a, T1, T2, U, FO, F>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1, T2) -> FO + Send,
        T1: 'a + Send,
        T2: 'a + Send,
    {
        Box::pin(async move {
            match (self.await, res1, res2) {
                (Ok(t), Ok(t1), Ok(t2)) => op(t, t1, t2).await,
                (Err(e), _, _) => Err(e),
                (_, Err(e1), _) => Err(e1),
                (_, _, Err(e2)) => Err(e2),
            }
        })
    }

    ///
    /// ```
    /// use railsgun::FutureResult;
    ///
    /// # async fn run() {
    /// fn func_xyz(v: u32, w: u32, x: u32, y: u32) -> Result<u32,u32> {
    ///     Ok( v + w + x + y)
    /// }
    ///
    /// let v = async {Ok(1u32) as Result<u32, u32>};
    /// let w = Ok(2);
    /// let x = Ok(2);
    /// let y = Ok(2);
    /// assert_eq!(v
    ///     .merge3(w, x, y,
    ///         |var_v, var_w, var_x, var_y|
    ///         async move {func_xyz(var_v, var_w, var_x, var_y)}
    ///     )
    ///     .await
    ///     .unwrap(), 7u32);
    /// # }
    /// ```
    #[inline]
    fn merge3<'a, T1, T2, T3, U, FO, F>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1, T2, T3) -> FO + Send,
        T1: 'a + Send,
        T2: 'a + Send,
        T3: 'a + Send,
    {
        Box::pin(async move {
            match (self.await, res1, res2, res3) {
                (Ok(t), Ok(t1), Ok(t2), Ok(t3)) => op(t, t1, t2, t3).await,
                (Err(e), _, _, _) => Err(e),
                (_, Err(e1), _, _) => Err(e1),
                (_, _, Err(e2), _) => Err(e2),
                (_, _, _, Err(e3)) => Err(e3),
            }
        })
    }

    ///
    /// ```
    /// use railsgun::FutureResult;
    ///
    /// # async fn run() {
    /// fn func_xyz(v: u32, w: u32, x: u32, y: u32, z: u32) -> Result<u32,u32> {
    ///     Ok( v + w + x + y + z)
    /// }
    ///
    /// let v = async {Ok(1u32) as Result<u32, u32>};
    /// let w = Ok(2);
    /// let x = Ok(2);
    /// let y = Ok(2);
    /// let z = Ok(2);
    /// assert_eq!(v
    ///     .merge4(w, x, y, z,
    ///         |var_v, var_w, var_x, var_y, var_z|
    ///         async move {func_xyz(var_v, var_w, var_x, var_y, var_z)}
    ///     )
    ///     .await
    ///     .unwrap(), 9u32);
    /// # }
    /// ```
    #[inline]
    fn merge4<'a, T1, T2, T3, T4, U, FO, F>(
        self,
        res1: Result<T1, E>,
        res2: Result<T2, E>,
        res3: Result<T3, E>,
        res4: Result<T4, E>,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        E: 'a,
        FO: Future<Output = Result<U, E>> + Send,
        F: 'a + FnOnce(T, T1, T2, T3, T4) -> FO + Send,
        T1: 'a + Send,
        T2: 'a + Send,
        T3: 'a + Send,
        T4: 'a + Send,
    {
        Box::pin(async move {
            match (self.await, res1, res2, res3, res4) {
                (Ok(t), Ok(t1), Ok(t2), Ok(t3), Ok(t4)) => op(t, t1, t2, t3, t4).await,
                (Err(e), _, _, _, _) => Err(e),
                (_, Err(e1), _, _, _) => Err(e1),
                (_, _, Err(e2), _, _) => Err(e2),
                (_, _, _, Err(e3), _) => Err(e3),
                (_, _, _, _, Err(e4)) => Err(e4),
            }
        })
    }
}

pub trait AsFutureResult<T, E> {
    fn as_async_result<'a>(self) -> Pin<Box<dyn Future<Output = Result<T, E>> + Send + 'a>>
    where
        Self: 'a;
}

impl<T: Send, E: Send> AsFutureResult<T, E> for Result<T, E> {
    fn as_async_result<'a>(self) -> Pin<Box<dyn Future<Output = Result<T, E>> + Send + 'a>>
    where
        Self: 'a,
    {
        Box::pin(async move { self })
    }
}

#[cfg(test)]
mod test {
    use super::FutureResult;
    use crate::future_result::AsFutureResult;

    #[tokio::test]
    async fn test_map() {
        async fn func_ok() -> Result<String, String> {
            Ok("foo".to_string())
        }

        async fn func_err() -> Result<String, String> {
            Err("foo".to_string())
        }

        assert_eq!(
            func_ok()
                .map(|t| async move { format!("Magic_ok: {}", t) })
                .map_err(|e| async move { format!("Magic_err: {}", e) })
                .await
                .unwrap(),
            "Magic_ok: foo".to_string()
        );
        assert_eq!(
            func_err()
                .map(|t| async move { format!("Magic_ok: {}", t) })
                .map_err(|e| async move { format!("Magic_err: {}", e) })
                .await
                .unwrap_err(),
            "Magic_err: foo".to_string()
        );
    }

    #[tokio::test]
    async fn test_map_or() {
        let x = async { Ok("foo") as Result<&str, &str> };
        assert_eq!(x.map_or(42, |v| async move { v.len() }).await, 3);

        let x = async { Err("bar") as Result<&str, &str> };
        assert_eq!(x.map_or(42, |v| async move { v.len() }).await, 42);
    }

    #[tokio::test]
    async fn test_map_err() {
        async fn stringify(x: i32) -> String {
            format!("error code: {}", x)
        }

        let x = async { Ok(2) as Result<i32, i32> };
        assert_eq!(x.map_err(stringify).await, Ok(2));

        let x = async { Err(13) as Result<i32, i32> };
        assert_eq!(
            x.map_err(stringify).await,
            Err("error code: 13".to_string())
        );
    }

    #[tokio::test]
    async fn test_and_then() {
        async fn sq(x: u32) -> Result<u32, u32> {
            Ok(x * x)
        }
        async fn err(x: u32) -> Result<u32, u32> {
            Err(x)
        }

        assert_eq!(async { Ok(2) }.and_then(sq).and_then(sq).await, Ok(16));
        assert_eq!(async { Ok(2) }.and_then(sq).and_then(err).await, Err(4));
        assert_eq!(async { Ok(2) }.and_then(err).and_then(sq).await, Err(2));
        assert_eq!(async { Err(3) }.and_then(sq).and_then(sq).await, Err(3));
    }

    #[tokio::test]
    async fn test_or_else() {
        async fn sq(x: u32) -> Result<u32, u32> {
            Ok(x * x)
        }
        async fn err(x: u32) -> Result<u32, u32> {
            Err(x)
        }
        assert_eq!(async { Ok(2) }.or_else(sq).or_else(sq).await, Ok(2));
        assert_eq!(async { Ok(2) }.or_else(err).or_else(sq).await, Ok(2));
        assert_eq!(async { Err(3) }.or_else(sq).or_else(err).await, Ok(9));
        assert_eq!(async { Err(3) }.or_else(err).or_else(err).await, Err(3));
    }

    #[tokio::test]
    async fn unwrap_or_else() {
        async fn count(x: &str) -> usize {
            x.len()
        }
        assert_eq!(async { Ok(2) }.unwrap_or_else(count).await, 2);
        assert_eq!(async { Err("foo") }.unwrap_or_else(count).await, 3);
    }

    #[tokio::test]
    async fn test_merge() {
        fn func_xyz(x: u32, y: u32) -> Result<u32, u32> {
            Ok(x + y)
        }

        let x = async { Ok(1u32) as Result<u32, u32> };
        let y = Ok(2);

        assert_eq!(
            x.merge(y, |var_x, var_y| async move { func_xyz(var_x, var_y) })
                .await
                .unwrap(),
            3u32
        );
    }

    #[tokio::test]
    async fn test_merge2() {
        fn func_xyz(v: u32, w: u32, x: u32) -> Result<u32, u32> {
            Ok(v + w + x)
        }

        let v = async { Ok(1u32) as Result<u32, u32> };
        let w = Ok(2);
        let x = Ok(2);
        assert_eq!(
            v.merge2(w, x, |var_v, var_w, var_x| async move {
                func_xyz(var_v, var_w, var_x)
            })
            .await
            .unwrap(),
            5u32
        );
    }

    #[tokio::test]
    async fn test_merge3() {
        fn func_xyz(v: u32, w: u32, x: u32, y: u32) -> Result<u32, u32> {
            Ok(v + w + x + y)
        }

        let v = async { Ok(1u32) as Result<u32, u32> };
        let w = Ok(2);
        let x = Ok(2);
        let y = Ok(2);
        assert_eq!(
            v.merge3(w, x, y, |var_v, var_w, var_x, var_y| async move {
                func_xyz(var_v, var_w, var_x, var_y)
            })
            .await
            .unwrap(),
            7u32
        );
    }

    #[tokio::test]
    async fn test_merge4() {
        fn func_xyz(v: u32, w: u32, x: u32, y: u32, z: u32) -> Result<u32, u32> {
            Ok(v + w + x + y + z)
        }

        let v = async { Ok(1u32) as Result<u32, u32> };
        let w = Ok(2);
        let x = Ok(2);
        let y = Ok(2);
        let z = Ok(2);
        assert_eq!(
            v.merge4(w, x, y, z, |var_v, var_w, var_x, var_y, var_z| async move {
                func_xyz(var_v, var_w, var_x, var_y, var_z)
            })
            .await
            .unwrap(),
            9u32
        );
    }

    #[tokio::test]
    async fn test_as_async_result() {
        fn func_xyz(x: u32, y: u32) -> Result<u32, u32> {
            Ok(x + y)
        }

        assert_eq!(
            func_xyz(3, 3)
                .as_async_result()
                .map(|t| async move { t + 3 })
                .await
                .unwrap(),
            9u32
        );
    }

    #[tokio::test]
    async fn test_as_async_result_struct() {
        struct FooBar {
            foo: String,
        }

        fn func_xyz() -> Result<FooBar, String> {
            Ok(FooBar {
                foo: "foo_foo".to_string(),
            })
        }

        assert_eq!(
            func_xyz()
                .as_async_result()
                .map(|t| async move { t.foo })
                .await
                .unwrap(),
            "foo_foo".to_string()
        );
    }
}
