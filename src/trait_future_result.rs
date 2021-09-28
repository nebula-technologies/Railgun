use core::pin::Pin;
use std::future::Future;

pub trait FutureResult<T, E> {
    fn map<'async_trait, U, F, TU>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        F: 'async_trait + FnOnce(T) -> TU + Send,
        TU: Future<Output = U> + Send;
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
    /// async fn async_function() -> String {
    ///   "foo".to_string();
    /// }
    ///
    /// # async fn run() -> () {
    /// let line = "1\n2\n3\n4\n";
    ///
    /// for num in line.lines() {
    ///     match num.parse::<i32>().map(|i| async move {i * 2}).await {
    ///         Ok(n) => println!("{}", n),
    ///         Err(..) => {}
    ///     }
    /// }
    /// # }
    /// ```
    fn map<'async_trait, U, F, TU>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        F: 'async_trait + (FnOnce(T) -> TU) + Send,
        TU: Future<Output = U> + Send,
    {
        Box::pin(async move {
            match self.await {
                Ok(t) => Ok(op(t).await),
                Err(e) => Err(e),
            }
        })
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
    /// async fn async_function() -> String {
    ///   "foo".to_string();
    /// }
    ///
    /// # async fn run() -> () {
    /// let line = "1\n2\n3\n4\n";
    ///
    /// for num in line.lines() {
    ///     match num.parse::<i32>().map(|i| async move {i * 2}).await {
    ///         Ok(n) => println!("{}", n),
    ///         Err(..) => {}
    ///     }
    /// }
    /// # }
    /// ```
    fn map<'async_trait, U, F, TU>(
        self,
        op: F,
    ) -> Pin<Box<dyn Future<Output = Result<U, E>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        F: 'async_trait + (FnOnce(T) -> TU) + Send,
        TU: Future<Output = U> + Send,
    {
        Box::pin(async move {
            match self.await {
                Ok(t) => Ok(op(t).await),
                Err(e) => Err(e),
            }
        })
    }
}

#[cfg(test)]
mod test {
    use super::FutureResult;

    async fn async_function() -> Result<String, String> {
        Ok("foo".to_string())
    }

    #[tokio::test]
    async fn test_map() -> () {
        let line = "1\n2\n3\n4\n";

        async_function()
            .map(|t| async move { format!("Magic: {}", t) })
            .await
            .and_then(|t| Err("bug".to_string()))
            .map(|t: String| println!("{}", t))
            .ok();
    }
}
