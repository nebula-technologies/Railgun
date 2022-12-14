use std::clone::Clone;
use std::marker::Send;
use std::thread;

pub trait TapRef<T, E> {
    fn tap_ref<F: FnOnce(&T)>(self, op: F) -> Self;
    fn tap_mut<F: FnOnce(&mut T)>(self, op: F) -> Self;
}

pub trait Tap<T, E> {
    fn tap<F: FnOnce(T)>(self, op: F) -> Self;
}
pub trait TapClone<T, E> {
    fn tap<F: FnOnce(T)>(self, op: F) -> Self;
}

pub trait TapErr<T, E> {
    fn tap_err<F: FnOnce(E)>(self, op: F) -> Self;
}
pub trait TapErrRef<T, E> {
    fn tap_err_ref<F: FnOnce(&E)>(self, op: F) -> Self;
    fn tap_err_mut<F: FnOnce(&mut E)>(self, op: F) -> Self;
}

pub trait ThreadTap<T, E> {
    fn thread_tap<F: 'static + FnOnce(T) + Send>(self, op: F) -> Self;
}
pub trait ThreadTapErr<T, E> {
    fn thread_tap_err<F: 'static + FnOnce(E) + Send>(self, op: F) -> Self;
}


/// # Result Tap Addition
///
///


/// # impl of TapRef [`Result<T,E>`]
/// This allows tapping into the result object and interact with a reference of the internal data.
impl<T, E> TapRef<T, E> for Result<T, E> {

    /// # tap_ref
    ///
    /// tap mut gives an immutable reference of the underlying data.
    /// this can often be used as way to log or read data in a cleaner fashion then using a map
    /// where you will hate to return the data anyways even if nothing has been modified.
    /// Taps does not rely on a return value.
    /// ```
    /// use railsgun::TapRef;
    ///
    /// let res: Result<_,()> = Ok("hello".to_string());
    /// res.tap_ref(|t| assert_eq!(t, &"hello".to_string())).ok();
    /// ```
    #[inline]
    fn tap_ref<F: FnOnce(&T)>(self, op: F) -> Result<T, E> {
        match &self {
            Ok(t) => { op(t); self },
            Err(_) => self,
        }
    }

    /// # tap_mut
    ///
    /// This allows for modifying the data that are recieved through tap.
    /// Normally map will to fine in this instance, though this allows for modifying the data
    /// behind the reference.
    /// The difference between map and tap_mut is that it operates directly on the reference and
    /// that the datatype is not allowed to change.
    /// ```
    /// use railsgun::TapRef;
    ///
    /// let res: Result<_,()> = Ok("hello".to_string());
    ///
    /// assert_eq!(res.tap_mut(|t| *t = "world".to_string()).unwrap(), "world".to_string());
    /// ```
    #[inline]
    fn tap_mut<F: FnOnce(&mut T)>(mut self, op: F) -> Self {
        match &mut self {
            Ok(t) => { op(t); self },
            Err(_) => self,
        }
    }
}

impl<T: Clone, E> TapClone<T, E> for Result<T, E> {
    #[inline]
    fn tap<F: FnOnce(T)>(self, op: F) -> Result<T, E> {
        if let Ok(ref ok) = self {
            op(ok.clone());
        }
        self
    }
}

impl<T, E: std::clone::Clone> TapErr<T, E> for Result<T, E> {
    #[inline]
    fn tap_err<F: FnOnce(E)>(self, op: F) -> Result<T, E> {
        if let Err(ref err) = self {
            op(err.clone());
        }
        self
    }
}

impl<T, E> TapErrRef<T, E> for Result<T, E> {

    /// # tap_err_ref
    ///
    /// tap mut gives an immutable reference of the underlying data.
    /// this can often be used as way to log or read data in a cleaner fashion then using a map
    /// where you will hate to return the data anyways even if nothing has been modified.
    /// Taps does not rely on a return value.
    ///
    /// This tap operates on the `Err` part of [`Result<T, E>`]
    /// ```
    /// use railsgun::TapErrRef;
    ///
    /// let res: Result<(), _> = Err("hello".to_string());
    /// res.tap_err_ref(|t| assert_eq!(t, &"hello".to_string())).ok();
    /// ```
    #[inline]
    fn tap_err_ref<F: FnOnce(&E)>(self, op: F) -> Result<T, E> {
        match &self {
            Ok(t) => self,
            Err(e) => { op(e); self }
        }
    }


    /// # tap_mut
    ///
    /// This allows for modifying the data that are recieved through tap.
    /// Normally map will to fine in this instance, though this allows for modifying the data
    /// behind the reference.
    /// The difference between map and tap_mut is that it operates directly on the reference and
    /// that the datatype is not allowed to change.
    ///
    /// This is operating only on the Err part of the [`Result<T, E>`]
    /// ```
    /// use railsgun::TapErrRef;
    ///
    /// let res: Result<(),_> = Err("hello".to_string());
    ///
    /// assert_eq!(res.tap_err_mut(|t| *t = "world".to_string()).unwrap_err(), "world".to_string());
    /// ```
    #[inline]
    fn tap_err_mut<F: FnOnce(&mut E)>(mut self, op: F) -> Result<T, E> {
        match &mut self {
            Ok(t) => self,
            Err(e) => { op(e); self }
        }
    }
}

impl<T: 'static + Clone + Send, E> ThreadTap<T, E> for Result<T, E> {
    #[inline]
    fn thread_tap<'a, F: 'static + FnOnce(T) + Send>(self, op: F) -> Result<T, E> {
        match self {
            Ok(ok) => {
                let new_ok = ok.clone();
                thread::spawn(move || op(new_ok));
                Ok(ok)
            }
            _ => self,
        }
    }
}

impl<T, E: 'static + Clone + Send> ThreadTapErr<T, E> for Result<T, E> {
    #[inline]
    fn thread_tap_err<F: 'static + FnOnce(E) + Send>(self, op: F) -> Result<T, E> {
        match self {
            Err(err) => {
                let new_err = err.clone();
                thread::spawn(move || op(new_err));
                Err(err)
            }
            _ => self,
        }
    }
}



impl<T> TapRef<T, ()> for Option<T> {
    /// # tap_ref
    ///
    /// tap mut gives an immutable reference of the underlying data.
    /// this can often be used as way to log or read data in a cleaner fashion then using a map
    /// where you will hate to return the data anyways even if nothing has been modified.
    /// Taps does not rely on a return value.
    /// ```
    /// use railsgun::TapRef;
    ///
    /// let res= Some("hello".to_string());
    /// res.tap_ref(|t| assert_eq!(t, &"hello".to_string()));
    /// ```
    #[inline]
    fn tap_ref<F: FnOnce(&T)>(self, op: F) -> Self {
        match &self {
            Some(t) => { op(t); self },
            None => { self }
        }
    }

    /// # tap_mut
    ///
    /// This allows for modifying the data that are recieved through tap.
    /// Normally map will to fine in this instance, though this allows for modifying the data
    /// behind the reference.
    /// The difference between map and tap_mut is that it operates directly on the reference and
    /// that the datatype is not allowed to change.
    /// ```
    /// use railsgun::TapRef;
    ///
    /// let res = Some("hello".to_string());
    ///
    /// assert_eq!(res.tap_mut(|t| *t = "world".to_string()).unwrap(), "world".to_string());
    /// ```
    #[inline]
    fn tap_mut<F: FnOnce(&mut T)>(mut self, op: F) -> Self {
        match &mut self {
            Some(t) => {  op(t); self },
            None => { self }
        }
    }
}

impl<T: Clone, E> TapClone<T, E> for Option<T> {
    #[inline]
    fn tap<F: FnOnce(T)>(self, op: F) -> Option<T> {
        if let Some(ref ok) = self {
            op(ok.clone());
        }
        self
    }
}

impl<T: Clone> TapErr<T, Option<T>> for Option<T>{
    #[inline]
    fn tap_err<F: FnOnce(Option<T>)>(self, op: F) -> Option<T> {
        if self.is_none() {
            op(self.clone());
        }
        self
    }
}

impl<T> TapErrRef<T, Option<T>> for Option<T> {
    #[inline]
    fn tap_err_ref<F: FnOnce(&Option<T>)>(self, op: F) -> Option<T> {
        match &self {
            Some(_) => self,
            None=> {op(&self); self}
        }
    }
    #[inline]
    fn tap_err_mut<F: FnOnce(&mut Option<T>)>(mut self, op: F) -> Option<T> {
        match &self {
            Some(_) => self,
            None=> {op(&mut self); self}
        }
    }
}

impl<T: 'static + Clone + Send, E> ThreadTap<T, E> for Option<T> {
    #[inline]
    fn thread_tap<'a, F: 'static + FnOnce(T) + Send>(self, op: F) -> Option<T> {
        match self {
            Some(some) => {
                let new_ok = some.clone();
                thread::spawn(move || op(new_ok));
                Some(some)
            }
            _ => self,
        }
    }
}

impl<T: 'static + Clone + Send> ThreadTapErr<T, Option<T>> for Option<T> {
    #[inline]
    fn thread_tap_err<F: 'static + FnOnce(Option<T>) + Send>(self, op: F) -> Option<T> {
        match self {
            None => {
                thread::spawn(move || op(self));
                None
            }
            _ => self,
        }
    }
}


#[cfg(test)]
pub mod test {
    use crate::TapRef;
    use crate::TapErrRef;

    #[test]
    pub async fn test_res_tap_ref() {
        let res: Result<_,()> = Ok("hello".to_string());
        res.tap_ref(|t| assert_eq!(t, &"hello".to_string())).ok();
    }

    #[test]
    pub async fn test_res_tap_mut() {
        let res: Result<_,()> = Ok("hello".to_string());

        assert_eq!(res.tap_mut(|t| *t = "world".to_string()).unwrap(), "world".to_string());
    }
    #[test]
    pub async fn test_opt_tap_ref() {
        let res = Some("hello".to_string());
        res.tap_ref(|t: &String| assert_eq!(t, &"hello".to_string()));
    }

    #[test]
    pub async fn test_opt_tap_mut() {
        let res = Some("hello".to_string());
        assert_eq!(res.tap_mut(|t| *t = "world".to_string()).unwrap(), "world".to_string());
    }

    #[test]
    pub async fn test_res_err_ref() {
        let res: Result<(), _> = Err("hello".to_string());
        res.tap_err_ref(|t| assert_eq!(t, &"hello".to_string())).ok();
    }

    #[test]
    pub async fn test_res_err_mut() {
        let res: Result<(),_> = Err("hello".to_string());
        assert_eq!(res.tap_err_mut(|t| *t = "world".to_string()).unwrap_err(), "world".to_string());
    }
}
