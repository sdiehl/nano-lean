use crate::kernel::Error;
use std::{fmt, thread};

const STACK_RED_ZONE: usize = 1 << 20;

/// Lowest address the calling thread's recursion may reach before it declines.
/// The red zone stays free for the unguarded leaves below the last guard.
pub(crate) fn stack_floor() -> usize {
    #[cfg(target_os = "macos")]
    // SAFETY: both calls only read the current thread's attributes.
    let (top, size) = unsafe {
        let t = libc::pthread_self();
        (
            libc::pthread_get_stackaddr_np(t) as usize,
            libc::pthread_get_stacksize_np(t),
        )
    };
    #[cfg(target_os = "linux")]
    // SAFETY: the attributes are initialized by pthread_getattr_np before being read and freed.
    let (top, size) = unsafe {
        let mut attr = std::mem::zeroed::<libc::pthread_attr_t>();
        let (mut base, mut size) = (std::ptr::null_mut(), 0);
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) == 0 {
            libc::pthread_attr_getstack(&attr, &mut base, &mut size);
            libc::pthread_attr_destroy(&mut attr);
        }
        (base as usize + size, size)
    };
    top - size + STACK_RED_ZONE.min(size / 2)
}

/// Run `f` on a fresh thread with a `bytes` stack, for recursion deeper than the caller's.
pub(crate) fn on_stack<T: Send>(bytes: usize, f: impl FnOnce() -> T + Send) -> T {
    thread::scope(|s| {
        thread::Builder::new()
            .stack_size(bytes)
            .spawn_scoped(s, f)
            .expect("spawn deep stack thread")
            .join()
            .unwrap_or_else(|p| std::panic::resume_unwind(p))
    })
}

/// Whether the caller's frame has reached `floor`.
#[inline(always)]
pub(crate) fn stack_exhausted(floor: usize) -> bool {
    let sp: usize;
    // SAFETY: reading the stack pointer touches no memory or flags.
    unsafe {
        #[cfg(target_arch = "aarch64")]
        std::arch::asm!("mov {}, sp", out(reg) sp, options(nomem, nostack, preserves_flags));
        #[cfg(target_arch = "x86_64")]
        std::arch::asm!("mov {}, rsp", out(reg) sp, options(nomem, nostack, preserves_flags));
    }
    sp < floor
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Budget {
    Work,
    Arena,
    Stack,
    Checking,
    NestedExpansion,
    UniverseComparison,
}

impl Budget {
    pub const fn message(self) -> &'static str {
        match self {
            Self::Work => "declaration work budget exhausted",
            Self::Arena => "declaration arena budget exhausted",
            Self::Stack => "declaration stack budget exhausted",
            Self::Checking => "checking budget exhausted",
            Self::NestedExpansion => "checking budget exhausted during nested expansion",
            Self::UniverseComparison => "universe comparison budget exhausted",
        }
    }
}

impl fmt::Display for Budget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message())
    }
}

impl From<Budget> for Error {
    #[cold]
    #[inline(never)]
    fn from(budget: Budget) -> Self {
        Error::Exhausted(budget)
    }
}
