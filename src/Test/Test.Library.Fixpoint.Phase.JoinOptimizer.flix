mod Test.Library.Fixpoint.Phase.JoinOptimizer {
    use Fixpoint.Phase.JoinOptimizer.powerSetOfSize
    
    ///
    /// Returns the powerset of `list`.
    ///
    def powerSet(list: List[a]): List[List[a]] = match list {
        case Nil => Nil :: Nil
        case x :: xs => 
            let ps = powerSet(xs);
            ps ::: List.map(ss -> x :: ss, ps)
    }

    @Test
    def testPowerSetOfSize(): Bool = 
        let k = 17;
        List.range(2,k) |> 
        List.forAll(i -> 
            let set = List.range(0, i);
            let ps1 = powerSet(set) |> List.filter(x -> List.length(x) == i) |> List.sort;
            let ps2 = powerSetOfSize(i, set);
            ps1 == ps2
        )

}