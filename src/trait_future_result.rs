use core::pin::Pin;
use std::future::Future;
use std::ops::{Deref, DerefMut};

pub trait FutureResult<T, E> {
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
        O: 'a + FnOnce(T) -> EO + Send,
        EO: Future<Output = Result<T, F>> + Send;

    fn async_unwrap_or_else<TO: Future<Output = T>, F: FnOnce(E) -> TO>(self, op: F) -> T {
        match self.inner {
            Result::Ok(t) => t,
            Result::Err(e) => op(e).await,
        }
    }

    fn async_merge<
        T1,
        U,
        FO: Future<Output = Result<U, E>>,
        F: FnOnce(T, T1) -> FO,
    >(
        self,
        res1: Result<T1, E>,
        op: F,
    )where
        FO: 'a + Future<Output = Result<U, E>> +Send;
    }
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
    /// use railsgun::FutureResult;
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
        Box::pin(async {
            match self.await {
                Ok(t) => f(t).await,
                Err(_) => default,
            }
        })
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
    /// use railsgun::FutureResult;
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
        Box::pin(async move {
            match self.await {
                Ok(t) => Ok(t),
                Err(e) => Err(op(e).await),
            }
        })
    }
}

#[cfg(test)]
mod test {
    use super::FutureResult;
    use std::future::Future;

    async fn async_function() -> Result<String, String> {
        Ok("foo".to_string())
    }

    #[tokio::test]
    async fn test_map() -> () {
        let line = "1\n2\n3\n4\n";

        async_function()
            .async_map(|t| async move { format!("Magic: {}", t) })
            .async_map(|t| async move { println!("{}", t) })
            .await
            .ok();
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
}
