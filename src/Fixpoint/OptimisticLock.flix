mod OptimisticLock {
    
    import java.util.concurrent.atomic.{AtomicLong => JAtomicLong}
    
    type alias Lock[r: Eff] = JAtomicLong

    // // Busy waiting for the lock.
    // Return the current value.
    pub def startRead(lock: Lock[r]): Int64 \ r = unchecked_cast({
        let val = lock.getAcquire();
        // let val = lock.get();
        val
        // // Check whether the returned value is even. If not try again. 
        // if (Int64.bitwiseAnd(val, 2i64) == 0i64) {
        //     val
        // } else 
        //     startRead(lock)
    } as _ \ r)
    // ???

    // 
    pub def valid(lease: Int64, lock: Lock[r]): Bool \ r =
        unchecked_cast(lock.get() == lease as _ \ r)

    // pub def endRead(lease: Int64, lock: Lock[r]): Bool = valid(lease, lock)

    pub def tryUpgradeToWrite(lease: Int64, lock: Lock[r]): Bool \ r = 
        unchecked_cast(lock.compareAndExchangeAcquire(lease, lease + 1i64) == lease + 1i64 as _ \ r)
    // ???

    pub def tryStartRead(lock: Lock[r]): Int64 \ r = 
        startRead(lock)
        // unchecked_cast(lock.get() as _ \ {r})

    pub def startWrite(): Unit = ??? 

    pub def abortWrite(): Unit = ???

    pub def endWrite(lock: Lock[r]): Unit \ r = 
        unchecked_cast({lock.getAndIncrement(); ()} as _ \ r)



    

}