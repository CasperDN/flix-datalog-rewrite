mod Fixpoint.Lock {
    import java.util.concurrent.locks.{ReentrantLock => JReentrantLock}
    
    pub type alias Lock[r: Eff] = JReentrantLock
    
    pub def mkLock(_: Region[r]): Lock[r] \ r = 
        unchecked_cast(new JReentrantLock() as _ \ r)

    pub def tryLock(lock: Lock[r]): Bool \ r =
        unchecked_cast(lock.tryLock() as _ \ r)

    pub def lock(lock: Lock[r]): Unit \ r =
        unchecked_cast(lock.lock() as _ \ r)

    pub def unlock(lock: Lock[r]): Unit \ r =
        unchecked_cast(lock.unlock() as _ \ r)

    
}