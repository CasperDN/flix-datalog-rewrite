
///
/// The purpose of this file is to record the transformation from Boxed values to Int64.
///

mod Fixpoint.BoxingTypes {
    use Fixpoint.Boxed
    use Fixpoint.Ast.Ram.RamId
    import java.util.concurrent.locks.{ReentrantReadWriteLock => JReadWriteLock}

    /// 
    /// A simple lock used for protecting correctness for multi-threaded programs.
    /// 
    @Internal
    pub enum Lock[_: Region](JReadWriteLock)

    mod Lock {
        import java.util.concurrent.locks.{ReentrantReadWriteLock => JReadWriteLock}
        use Fixpoint.BoxingTypes.Lock

        pub def mkLock(_: Region[r]): Lock[r] \ r =
            Lock(unchecked_cast((new JReadWriteLock(): _ \ IO) as _ \ r))

        pub def readLock(lock: Lock[r]): Unit \ r =
            let Lock(l) = lock;
            unchecked_cast((l.readLock().lock(): _ \ IO) as _ \ r)

        pub def writeLock(lock: Lock[r]): Unit \ r =
            let Lock(l) = lock;
            unchecked_cast((l.writeLock().lock(): _ \ IO) as _ \ r)

        pub def unlockRead(lock: Lock[r]): Unit \ r =
            let Lock(l) = lock;
            unchecked_cast((l.readLock().unlock(): _ \ IO) as _ \ r)

        pub def unlockWrite(lock: Lock[r]): Unit \ r =
            let Lock(l) = lock;
            unchecked_cast((l.writeLock().unlock(): _ \ IO) as _ \ r)
    }

    ///
    /// `Types` represent the different types a program can contain
    ///
    @Internal
    pub enum Types {
        case Unknown
        case Bool
        case Char
        case Int8
        case Int16
        case Int32
        case Int64
        case Float32
        case Float64
        case Object
    }

    ///
    /// Describes the placement of type-information of a group of values that share the same type
    ///
    @Internal
    pub type alias UnifiedTypePos = Int32    

    ///
    /// `RamIdToMarshal` maps `RamId` to the `UnifiedTypePos`. It facilitates getting the type-information
    /// of a `RamTerm`.
    ///
    @Internal
    pub type alias RamIdToPos = Map[RamId, UnifiedTypePos]

    /// 
    /// `TypeInfo` describes the type of values. The `UnifiedTypePos` describes where in `TypeInfo`
    /// the type of a specific value can be found
    /// 
    enum TypeInfo[r: Region] {
        case TypeInfo(Array[Types, r])
    }

    ///
    /// Store the type `t` of a value saved at `index` in `typeInfo`.
    ///
    @Internal
    pub def setType(t: Types, index: UnifiedTypePos, typeInfo: TypeInfo[r]): Unit \ r = match typeInfo {
        case TypeInfo.TypeInfo(arr) => Array.put(t, index, arr)
    }

    ///
    /// Return the type of value saved at `index` in `typeInfo`.
    ///
    @Internal
    pub def getType(index: Int32, typeInfo: TypeInfo[r]): Types \ r = match typeInfo {
        case TypeInfo.TypeInfo(arr) => Array.get(index, arr)
    }

    ///
    /// `Boxing=(values, valueToRep, typeInfo, locks)` represents the combined knowledge
    /// that is needed to convert between Boxed objects and their Int64 representation
    /// 
    /// The i'th value of each Vector belongs to a specific `UnifiedTypePos`. The
    /// description of the values will be for some `i`.
    /// 
    /// `valueToRep` maps Boxed objects to their Int64 representation.
    ///
    /// `values` contains the Boxed objects being stored.
    ///
    /// The following invariant is kept `values(valueToRep[boxedValue]) == boxedValue`. This
    /// design limits us to 2^32 objects of a given type.
    ///
    /// `locks[i]` must be acquired before a specific `values[i]` or `valueToRep[i]` can be
    /// interacted with. 
    ///
    @Internal
    pub type alias Boxing[r: Region] = (
        Vector[MutList[Boxed, r]], // List of Boxed objects 
        Vector[MutMap[Boxed, Int64, r]], // [RelSym->IndexInTyple->BoxedObject->Int64]
        TypeInfo[r],
        Vector[Lock[r]], // Locks on the MutList/MutMap.
    )
}