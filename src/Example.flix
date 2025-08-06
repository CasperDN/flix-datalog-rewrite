def latticeTest(): Unit \ IO =
    println("Starting");
    let func = () -> {
        let start = Clock.currentTime(TimeUnit.Seconds);
        let map = List.map(x -> (x, x + 1), List.range(1, 200));
        let injected = inject map into Edge/2;
        let path = injected <+> #{
            Path(x, y; Down.Down(1)) :- Edge(x, y).
            Path(x, y; n + Down.Down(1)) :- Path(x, z; n), Edge(z, y).
        };
        let r = query path select (x, y, set) from Path(x,y; set);
        let x = Vector.head(r);
        if (Option.isEmpty(x)) {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        } else {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        }
    };
    Clock.runWithIO(() -> repeatN(func, 10))

def main(): Unit \ IO =
    println("Starting");
    let func = () -> {
        let start = Clock.currentTime(TimeUnit.Seconds);
        let map = List.map(x -> (x, x + 1), List.range(1, 1000));
        let injected = inject map into Edge/2;
        let path = injected <+> #{
            Edge(x, y) :- Edge(y, x).
            Path(x, y) :- Edge(x, y).
            Path(x, y) :- Path(x, z), Edge(z, y).
        };
        let r = query path select (x, y) from Path(x,y);
        let x = Vector.head(r);
        if (Option.isEmpty(x)) {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        } else {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        }
    };
    Clock.runWithIO(() -> repeatN(func, 10));
    ()

def repeatN(f: Unit -> Unit \ ef, num: Int32): Unit \ef =
    if (num <= 0) {
        ()
    } else {
        f();
        repeatN(f, num - 1)
    }

def ++++++(x: Int32, y: Int32): Int32 = Int32.modulo(x, y)

def isPrime(x: Int32): Bool =
    def loop(i) =
        if (i > x / 2) true
        else if (x ++++++ i == 0) false
        else loop(i+1);
    if (x < 2) false
    else loop(2)

def primesInRange(b: Int32, e: Int32): Vector[Int32] =
    Vector.range(b, e) |> Vector.filter(isPrime)

def inc(x: Int32): Int32 = x + 1

def main3(): Unit \ IO =
    let r = #{
        P(1).
        Q(20).
        R(p, inc(p)) :- P(b), Q(e), let p = primesInRange(b, e).
    };
    println(query r select (p, q) from R(p, q))

pub def main111(): Unit \ IO =
    let rules = #{
        Foo("a", 1).
        Foo("b", 2).

        Bar(n; v) :- Foo(n, v).
    };
    query rules select (x, y) from Bar(x; y) |> println;
    ()

def main99(): Unit \ IO =
    println("Print");
    let path = #{
        Edge(1,2).

        Path(x, y) :- Edge(x, y).
        Path(x, y) :- Path(x, z), Path(z, y).
    };
    let indexSelection1 = #{
        A(1, 2, 3).
        B(1, 2, 3).
        B(x, y, z) :- A(x, y, z), B(x, _, z).
        B(x, y, z) :- A(x, y, z), B(x, _, _).
        B(x, y, z) :- A(x, y, z), B(x, y, _).
        B(x, y, z) :- A(x, y, z), B(x, y, z).
    };
    let indexSelection2 = #{
        A(1, 2, 3).
        B(1, 2, 3).
        B(x, y, z) :- A(x, y, z), B(x, _, z).
        B(x, y, z) :- A(x, y, z), B(x, y, _).
        B(x, y, z) :- A(x, y, z), B(x, y, z).
    };
    println("Print2");
    let _ = query path select (x, y) from Path(x,y);
    println("Print3");
    let r = query indexSelection1 select (x, y, z) from B(x, y, z);
    println("Print4");
    let _ = query indexSelection2 select (x, y, z) from B(x, y, z);
    println("Print5");
    println(r);
    println("Print6");
    ()

def sum1(x: Int32): Int32 = x
def sum2(x: Int32, y: Int32): Int32 = x + y
def sum3(x: Int32, y: Int32, z: Int32): Int32 = x + y + z
def sum4(x: Int32, y: Int32, z: Int32, w: Int32): Int32 = x + y + z + w
def sum5(x: Int32, y: Int32, z: Int32, w: Int32, v: Int32): Int32 = x + y + z + w + v

pub def mainApp(): Unit \ IO =
    let rules = #{
        Foo1(1).
        Foo2(2).
        Foo3(3).
        Foo4(4).
        Foo5(5).

        Bar(a,
            sum1(a),
            sum2(a, b),
            sum3(a, b, c),
            sum4(a, b, c, d),
            sum5(a, b, c, d, e)
        ) :- Foo1(a), Foo2(b), Foo3(c), Foo4(d), Foo5(e).
    };
    query rules select (a, b, c, d, e, f) from Bar(a, b, c, d, e, f) |> println;
    ()

pub def pathh(): Unit \ IO =
    let edges = List.range(0,1000) |> List.map(i -> (i, i+1));
    let f = inject edges into Edge/2;
    let r = #{
        A(1).
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Edge(y, z), Path(x, y).
        // DumbRule(1,2,3) :- Path(x, 1), A(x).
    };
    query f, r select (x, y) from Path(x, y) |> Vector.head |> println

pub def dumb3333(): Unit \ IO =
    let r = #{
        A(1).
    };
    query r select x from A(x) |> Vector.head |> println;
    ()

pub def dumb(): Unit \ IO =
    let aFacts = List.range(0,101);
    let bFacts = List.range(0,10);
    let f1 = inject aFacts into A/1;
    let f2 = inject bFacts into B/1;
    let r = #{
        A(x) :- D(x).
        D(x) :- A(x).
        B(x) :- D(x).
        C(x) :- A(x), B(x).
    };
    query f1, f2, r select x from C(x)  |> println;
    ()


def forceEval(): Unit \ IO = {
    println("Hej")
}


def testFunctionalF1X2_01(): Bool =
let ff = _x -> Vector#{};
    let pr = #{
        A(1).
        R(a, b) :- A(x), let (a, b) = ff(x).
    };
    let actual = query pr select (x, y) from R(x, y);
    Assert.eq((Vector#{}: Vector[(Int32, Int32)]), actual)

def runForever(): Unit \ IO = {
    if (testFunctionalF1X2_01()) runForever() else runForever()
}


def runN(n: Int32): Unit \ IO = {
    if (testFunctionalF1X2_01() and n > 0) runN(n - 1) else ()
}

def main1000(): Unit \ IO = {
    let now = Clock.runWithIO(Clock.now);
    runN(80000);
    println((Clock.runWithIO(Clock.now) - now) / 1000i64);
    ()
}
