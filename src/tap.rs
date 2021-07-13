use std::clone::Clone;
use std::marker::Send;
use std::thread;

pub trait Tap<T, E> {
    fn tap<F: FnOnce(T)>(self, op: F) -> Result<T, E>;
}

pub trait TapErr<T, E> {
    fn tap_err<F: FnOnce(E)>(self, op: F) -> Result<T, E>;
}

pub trait ThreadTap<T, E> {
    fn thread_tap<F: 'static + FnOnce(T) + Send>(self, op: F) -> Result<T, E>;
}
pub trait ThreadTapErr<T, E> {
    fn thread_tap_err<F: 'static + FnOnce(E) + Send>(self, op: F) -> Result<T, E>;
}

impl<T: std::clone::Clone, E> Tap<T, E> for Result<T, E> {
    fn tap<F: FnOnce(T)>(self, op: F) -> Result<T, E> {
        match self {
            Ok(ref ok) => {
                op(ok.clone());
            }
            _ => {}
        }
        self
    }
}

impl<T, E: std::clone::Clone> TapErr<T, E> for Result<T, E> {
    fn tap_err<F: FnOnce(E)>(self, op: F) -> Result<T, E> {
        match self {
            Err(ref err) => {
                op(err.clone());
            }
            _ => {}
        }
        self
    }
}

impl<T: 'static + Clone + Send, E> ThreadTap<T, E> for Result<T, E> {
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
