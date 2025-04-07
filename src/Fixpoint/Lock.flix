
mod Fixpoint {
    import java.util.concurrent.locks.{ReentrantLock => JReentrantLock}
    @Internal
    pub enum Lock[_: Region](JReentrantLock)
}
mod Fixpoint.Lock {
    import java.util.concurrent.locks.Lock
    import java.util.concurrent.locks.{ReentrantLock => JReentrantLock}
        
    pub def mkLock(_: Region[r]): Fixpoint.Lock[r] \ r = 
        Lock(unchecked_cast((new JReentrantLock(): _ \ IO) as _ \ r))

    pub def tryLock(lock: Fixpoint.Lock[r]): Bool \ r =
        let Lock(l) = lock;
        unchecked_cast((l.tryLock(): _ \ IO) as _ \ r)

    pub def lock(lock: Fixpoint.Lock[r]): Unit \ r =
        let Lock(l) = lock;
        unchecked_cast((l.lock(): _ \ IO) as _ \ r)

    pub def unlock(lock: Fixpoint.Lock[r]): Unit \ r =
        let Lock(l) = lock;
        unchecked_cast((l.unlock(): _ \ IO) as _ \ r)
}