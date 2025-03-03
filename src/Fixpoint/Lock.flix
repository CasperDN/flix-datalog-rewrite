mod Fixpoint.ReadWriteLock {
    import java.util.concurrent.locks.ReentrantReadWriteLock
    
    pub type alias ReadWriteLock[r: Eff] = ReentrantReadWriteLock
    
    pub def mkLock(_: Region[r]): ReadWriteLock[r] \ r = 
        unchecked_cast(new ReentrantReadWriteLock() as _ \ r)

    pub def tryReadLock(lock: ReadWriteLock[r]): Bool \ r =
        unchecked_cast(lock.readLock().tryLock() as _ \ r)

    pub def tryWriteLock(lock: ReadWriteLock[r]): Bool \ r =
        unchecked_cast(lock.writeLock().tryLock() as _ \ r)

    pub def writeLock(lock: ReadWriteLock[r]): Unit \ r =
        unchecked_cast(lock.writeLock().lock() as _ \ r)

    pub def readLock(lock: ReadWriteLock[r]): Unit \ r =
        unchecked_cast(lock.readLock().lock() as _ \ r)

    pub def unlockReadLock(lock: ReadWriteLock[r]): Unit \ r =
        unchecked_cast(lock.readLock().unlock() as _ \ r)

    pub def unlockWritelock(lock: ReadWriteLock[r]): Unit \ r =
        unchecked_cast(lock.writeLock().unlock() as _ \ r)

    
}