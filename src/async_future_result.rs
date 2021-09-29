use crate::FutureResult;
use core::pin::Pin;
use std::future::Future;

pub trait AsyncFutureResult<T, E>: FutureResult<T, E> {
    fn async_map<'a, U, F, TU>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> TU + Send,
        TU: Future<Output = U> + Send;

    fn async_map_or<'a, U, UO, F>(
        self,
        default: U,
        f: F,
    ) -> Pin<Box<dyn Future<Output = U> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> UO + Send,
        UO: Future<Output = U> + Send,
        U: 'a + Send;

    fn async_map_err<'a, F, UO, O>(
        self,
        op: O,
    ) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> UO + Send,
        UO: Future<Output = F> + Send;

    fn async_and_then<'a, U, F, FO>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> FO + Send,
        FO: Future<Output = Result<U, E>> + Send;

    fn async_or_else<'a, F, EO, O>(
        self,
        op: O,
    ) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> EO + Send,
        EO: Future<Output = Result<T, F>> + Send;

    fn async_unwrap_or_else<'a, TO, F>(self, op: F) -> Pin<Box<dyn Future<Output = T> + Send + 'a>>
    where
        Self: 'a,
        TO: Future<Output = T> + Send,
        F: 'a + FnOnce(E) -> TO + Send;

    fn async_merge<'a, T1, U, FO, F>(
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
}

impl<T: Send, E: Send, L> AsyncFutureResult<T, E> for L
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
    /// use railsgun::AsyncFutureResult;
    /// async fn async_function() -> Result<String, String> {
    ///    Ok("foo".to_string())
    /// }
    ///
    /// # async fn run() -> () {
    /// async_function()
    ///     .async_map(|t| async move { format!("Magic: {}", t) })
    ///     .async_map(|t| async move { println!("{}", t) })
    ///     .await
    ///     .ok();
    /// # }
    /// ```
    fn async_map<'a, U, F, TU>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + (FnOnce(T) -> TU) + Send,
        TU: Future<Output = U> + Send,
    {
        self.map(op)
    }

    /// Applies a function to the contained value (if [`Ok`]),
    /// or returns the provided default (if [`Err`]).
    ///
    /// Arguments passed to `async_map_or` are eagerly evaluated; if you are passing
    /// the Result of a function call, it is recommended to use [`map_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`map_or_else`]: Result::async_map_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::future::Future;
    /// use railsgun::AsyncFutureResult;
    ///
    ///  async fn run() -> () {
    /// let x = async {Ok("foo") as Result<&str, &str>};
    /// assert_eq!(x.async_map_or(42, |v| async move {v.len()}).await, 3);
    ///
    /// let x = async{Err("bar") as Result<&str, &str>};
    /// assert_eq!(x.async_map_or(42, |v| async move {v.len()}).await, 42);
    /// # }
    /// ```
    #[inline]
    fn async_map_or<'a, U, UO, F>(
        self,
        default: U,
        f: F,
    ) -> Pin<Box<dyn Future<Output = U> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> UO + Send,
        UO: Future<Output = U> + Send,
        U: 'a + Send,
    {
        self.map_or(default, f)
    }

    /// Maps a `AsyncResult<T, E>` to `AsyncResult<T, F>` by applying a function to a
    /// contained [`Err`] value, leaving an [`Ok`] value untouched.
    ///
    /// This function can be used to pass through a successful AsyncResult while handling
    /// an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use std::future::Future;
    /// use railsgun::AsyncFutureResult;
    /// async fn stringify(x: i32) -> String{ format!("error code: {}", x) }
    ///
    /// # async fn run() -> () {
    /// let x = async {Ok(2) as Result<i32, i32>};
    /// assert_eq!(x.async_map_err(stringify).await, Ok(2));
    ///
    /// let x = async {Err(13) as Result<i32, i32>};
    /// assert_eq!(x.async_map_err(stringify).await, Err("error code: 13".to_string()));
    /// # }
    /// ```
    fn async_map_err<'a, F, UO, O>(
        self,
        op: O,
    ) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> UO + Send,
        UO: Future<Output = F> + Send,
    {
        self.map_err(op)
    }

    /// Calls `op` if the AsyncResult is [`Ok`], otherwise returns the [`Err`] value of `self`.
    ///
    ///
    /// This function can be used for control flow based on `AsyncResult` values.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use std::future::Future;
    /// use railsgun::AsyncFutureResult;
    ///
    /// # async fn run() -> () {
    ///
    /// async fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
    /// async fn err(x: u32) -> Result<u32, u32> { Err(x) }
    ///
    /// assert_eq!(async{Ok(2)}.async_and_then(sq).async_and_then(sq).await, Ok(16));
    /// assert_eq!(async{Ok(2)}.async_and_then(sq).async_and_then(err).await, Err(4));
    /// assert_eq!(async{Ok(2)}.async_and_then(err).async_and_then(sq).await, Err(2));
    /// assert_eq!(async{Err(3)}.async_and_then(sq).async_and_then(sq).await, Err(3));
    /// # }
    /// ```
    fn async_and_then<'a, U, F, FO>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'a>>
    where
        Self: 'a,
        F: 'a + FnOnce(T) -> FO + Send,
        FO: Future<Output = Result<U, E>> + Send,
    {
        self.and_then(op)
    }
    /// Calls `op` if the AsyncResult is [`Err`], otherwise returns the [`Ok`] value of `self`.
    ///
    /// This function can be used for control flow based on AsyncResult values.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railsgun::AsyncFutureResult;
    ///
    /// async fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
    /// async fn err(x: u32) -> Result<u32, u32> { Err(x) }
    ///
    /// # async fn run() -> () {
    /// assert_eq!(async{Ok(2)}.async_or_else(sq).async_or_else(sq).await, Ok(2));
    /// assert_eq!(async{Ok(2)}.async_or_else(err).async_or_else(sq).await, Ok(2));
    /// assert_eq!(async{Err(3)}.async_or_else(sq).async_or_else(err).await, Ok(9));
    /// assert_eq!(async{Err(3)}.async_or_else(err).async_or_else(err).await, Err(3));
    /// # }
    /// ```
    fn async_or_else<'a, F, EO, O>(
        self,
        op: O,
    ) -> Pin<Box<dyn Future<Output = Result<T, F>> + Send + 'a>>
    where
        Self: 'a,
        O: 'a + FnOnce(E) -> EO + Send,
        EO: Future<Output = Result<T, F>> + Send,
    {
        self.or_else(op)
    }
    /// Returns the contained [`Ok`] value or computes it from a closure.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railsgun::AsyncFutureResult;
    ///
    /// async fn count(x: &str) -> usize { x.len() }
    ///
    /// # async fn run() -> () {
    /// assert_eq!(async{Ok(2)}.async_unwrap_or_else(count).await, 2);
    /// assert_eq!(async{Err("foo")}.async_unwrap_or_else(count).await, 3);
    /// # }
    /// ```
    fn async_unwrap_or_else<'a, TO, F>(self, op: F) -> Pin<Box<dyn Future<Output = T> + Send + 'a>>
    where
        Self: 'a,
        TO: Future<Output = T> + Send,
        F: 'a + FnOnce(E) -> TO + Send,
    {
        self.unwrap_or_else(op)
    }

    /// ```
    /// use railsgun::AsyncFutureResult;
    ///
    /// # async fn run() {
    /// fn func_xyz(x: u32, y: u32) -> Result<u32,u32> {
    ///     Ok( x + y)
    /// }
    ///
    /// let x = async {Ok(1u32) as Result<u32, u32>};
    /// let y = Ok(2);
    ///
    /// x.async_merge(y, |var_x, var_y,| async move {func_xyz(var_x, var_y)})
    ///     .await
    ///     .ok();
    /// # }
    /// ```
    fn async_merge<'a, T1, U, FO, F>(
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
        self.merge(res1, op)
    }
}

#[cfg(test)]
mod test {
    use crate::AsyncFutureResult;

    #[tokio::test]
    async fn test_map() {
        async fn async_function() -> Result<String, String> {
            Ok("foo".to_string())
        }

        async_function()
            .async_map(|t| async move { format!("Magic: {}", t) })
            .async_map(|t| async move { println!("{}", t) })
            .await
            .ok();
    }

    #[tokio::test]
    async fn test_map_or() {
        let x = async { Ok("foo") as Result<&str, &str> };
        assert_eq!(x.async_map_or(42, |v| async move { v.len() }).await, 3);

        let x = async { Err("bar") as Result<&str, &str> };
        assert_eq!(x.async_map_or(42, |v| async move { v.len() }).await, 42);
    }

    #[tokio::test]
    async fn test_map_err() {
        async fn stringify(x: i32) -> String {
            format!("error code: {}", x)
        }

        let x = async { Ok(2) as Result<i32, i32> };
        assert_eq!(x.async_map_err(stringify).await, Ok(2));

        let x = async { Err(13) as Result<i32, i32> };
        assert_eq!(
            x.async_map_err(stringify).await,
            Err("error code: 13".to_string())
        );
    }

    #[tokio::test]
    async fn test_async_and_then() {
        async fn sq(x: u32) -> Result<u32, u32> {
            Ok(x * x)
        }
        async fn err(x: u32) -> Result<u32, u32> {
            Err(x)
        }

        assert_eq!(
            async { Ok(2) }.async_and_then(sq).async_and_then(sq).await,
            Ok(16)
        );
        assert_eq!(
            async { Ok(2) }.async_and_then(sq).async_and_then(err).await,
            Err(4)
        );
        assert_eq!(
            async { Ok(2) }.async_and_then(err).async_and_then(sq).await,
            Err(2)
        );
        assert_eq!(
            async { Err(3) }.async_and_then(sq).async_and_then(sq).await,
            Err(3)
        );
    }

    #[tokio::test]
    async fn test_async_or_else() {
        async fn sq(x: u32) -> Result<u32, u32> {
            Ok(x * x)
        }
        async fn err(x: u32) -> Result<u32, u32> {
            Err(x)
        }
        assert_eq!(
            async { Ok(2) }.async_or_else(sq).async_or_else(sq).await,
            Ok(2)
        );
        assert_eq!(
            async { Ok(2) }.async_or_else(err).async_or_else(sq).await,
            Ok(2)
        );
        assert_eq!(
            async { Err(3) }.async_or_else(sq).async_or_else(err).await,
            Ok(9)
        );
        assert_eq!(
            async { Err(3) }.async_or_else(err).async_or_else(err).await,
            Err(3)
        );
    }

    #[tokio::test]
    async fn async_unwrap_or_else() {
        async fn count(x: &str) -> usize {
            x.len()
        }
        assert_eq!(async { Ok(2) }.async_unwrap_or_else(count).await, 2);
        assert_eq!(async { Err("foo") }.async_unwrap_or_else(count).await, 3);
    }

    #[tokio::test]
    async fn run() {
        fn func_xyz(x: u32, y: u32) -> Result<u32, u32> {
            Ok(x + y)
        }

        let x = async { Ok(1u32) as Result<u32, u32> };
        let y = Ok(2);

        x.async_merge(y, |var_x, var_y| async move { func_xyz(var_x, var_y) })
            .await
            .ok();
    }
}
