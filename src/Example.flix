def ex1_01(): Unit \ IO = 
    let facts = #{
        // The Simpsons family tree
        Male("Abraham").
        Male("Clancy").
        Male("Herb").
        Male("Homer").
        Male("Bart").
        Female("Mona").
        Female("Jackie").
        Female("Marge").
        Female("Patty").
        Female("Lisa").
        Female("Maggie").
        Female("Selma").
        Female("Ling").

        Parent("Homer", "Abraham").
        Parent("Homer", "Mona").
        Parent("Herb", "Abraham"). // Herb's mother is not Mona and we dont consider half-uncles as uncles below
        Parent("Marge", "Clancy").
        Parent("Marge", "Jackie").
        Parent("Bart", "Homer").
        Parent("Bart", "Marge").
        Parent("Lisa", "Homer").
        Parent("Lisa", "Marge").
        Parent("Maggie", "Homer").
        Parent("Maggie", "Marge").
        Parent("Selma", "Clancy").
        Parent("Selma", "Jackie").
        Parent("Patty", "Clancy").
        Parent("Patty", "Jackie").
        Parent("Ling", "Selma").
    };
    let rules = #{
        Father(child, dad) :- Parent(child, dad), Male(dad). // A father is a male parent
        Mother(child, mum) :- Parent(child, mum), Female(mum). // A mother is a female parent

        // A brother/sister is male/female and has the same parents as the sibling
        Brother(sibling, brother) :- Father(sibling, dad), Father(brother, dad),
                                       Mother(sibling, mum), Mother(brother, mum),
                                       Male(brother), if (sibling != brother).
        Sister(sibling, sister) :- Father(sibling, dad), Father(sister, dad), 
                                      Mother(sibling, mum), Mother(sister, mum),
                                      Female(sister), if (sibling != sister).

        // An uncle/aunt is the brother/sister of a nibling's parent
        Uncle(nibling, uncle) :- Parent(nibling, parent), Brother(parent, uncle).
        Aunt(nibling, aunt) :- Parent(nibling, parent), Sister(parent, aunt).

    };
    println("Father:");
    query facts, rules select (sibling, brother) from Father(sibling, brother) |> println;
    println("Mother:");
    query facts, rules select (sibling, brother) from Mother(sibling, brother) |> println;
    println("Brothers:");
    query facts, rules select (sibling, brother) from Brother(sibling, brother) |> println;
    println("Sisters:");
    query facts, rules select (sibling, sister) from Sister(sibling, sister) |> println;
    println("Uncles:");
    query facts, rules select (nibling, uncle) from Uncle(nibling, uncle) |> println;
    println("Aunts:");
    query facts, rules select (sibling, aunt) from Aunt(sibling, aunt) |> println;
    ()

def ex1__04(): Unit \ IO = 
    let facts = #{
        Road("Aarhus", "Vejle").
        Road("Aarhus", "Aalborg").
        Road("Aalborg", "Skagen").
        Road("Billund", "Vejle").
        Road("Odense", "Vejle").
        Road("Odense", "Nyborg").
        Road("Helsingør", "København").
        Road("Helsingborg", "Malmø").
        // Road("Korsør", "Nyborg"). // Mistake? Korsør -> Nyborg requires crossing Storebælt?
        Road("Korsør", "Roskilde").
        Road("København", "Roskilde").
        Road("Rønne", "Nexø").

        Bridge("Storebælt", "Korsør", "Nyborg").
        Bridge("Øresund", "København", "Malmø").
        Bridge("Nivå", "Helsingborg", "Helsingør").

        Flight("Aalborg", "København").
        Flight("Aarhus", "København").
        Flight("Billund", "København").
        Flight("København", "Rønne").
    };
    let rules = #{
        Road(src, dst) :- Road(dst, src). // Roads are bi-directional
        Bridge(name, src, dst) :- Bridge(name, dst, src). // Bridges are bi-directional
        Flight(src, dst) :- Flight(dst, src). // Flights are bi-directional

        Drivable(src, dst) :- Road(src, dst). 
        Drivable(src, dst) :- Drivable(src, mid), Drivable(mid, dst), if (src != dst). // Transitivity

        DrivableWithBridges(src, dst) :- Drivable(src, dst).
        DrivableWithBridges(src, dst) :- Bridge(name, src, dst).
        DrivableWithBridges(src, dst) :- DrivableWithBridges(src, mid), Bridge(name, mid, dst), if (src != dst).
        DrivableWithBridges(src, dst) :- Bridge(name, src, mid), DrivableWithBridges(mid, dst), if (src != dst).

        FlightTo(src, dst) :- Flight(src, dst).
        FlightTo(src, dst) :- Flight(src, mid), Flight(mid, dst), if (src != dst).

        Reachable(src, dst) :- DrivableWithBridges(src, mid), FlightTo(mid, dst).
    };
    println("Cities one can drive to from Odense:");
    query facts, rules select dst from Drivable("Odense", dst) |> println;
    println("\nCities one can drive to from Skagen, possibly using bridges:");
    query facts, rules select dst from DrivableWithBridges("Skagen", dst) |> println;
    println("\nIs it possible to travel from Nexø to Aalborg?");
    not Vector.isEmpty(query facts, rules select true from Reachable("Nexø", "Aalborg")) |> println;
    println("\nIs it possible to travel from Aalborg to Nexø?");
    not Vector.isEmpty(query facts, rules select true from Reachable("Aalborg", "Nexø"))|> println;
    ()

def ex1_12(): Unit \ IO = 
    let facts = #{
        Road("Brundisium", "Capua").
        Road("Brundisium", "Tarentum").
        Road("Capua", "Tarentum").
        Road("Capua", "Rome").
        Road("Genua", "Massilia").
        Road("Genua", "Pisae").
        Road("Genua", "Parma").
        Road("Messana", "Syracuse").
        Road("Ostia", "Rome").
        Road("Parma", "Ravenna").
        Road("Pisae", "Ravenna").
        Road("Pisae", "Rome").
    };
    let rules = #{
        Road(src, dst) :- Road(dst, src).

        ThroughRome(src, dst) :- Road(src, "Rome"), Road("Rome", dst), if (src != dst).
        ThroughRome(src, dst) :- Road(src, mid), ThroughRome(mid, dst), if (src != dst and src != "Rome" and dst != "Rome").
        ThroughRome(src, dst) :- ThroughRome(src, mid), Road(mid, dst), if (src != dst and src != "Rome" and dst != "Rome").
    };
    query facts, rules select (src,dst) from ThroughRome(src, dst) |> println

def ex1_13(): Unit \ IO = 
    let facts = #{
        // Available hardware.
        Machine("x86").
        Machine("x64").

        // Available interpreters (JITs).
        Interpreter("JavaScript", "C++").  // A JavaScript interpreter written in C++.
        Interpreter("JVM", "C++").
        Interpreter("WASM", "C++").

        // Modern compilers.
        Compiler("C", "x86", "C").
        Compiler("C", "x64", "C").
        Compiler("C++", "x86", "C").       // A compiler from C++ to x86 written in C.
        Compiler("C++", "x64", "C").
        Compiler("Flix", "JVM", "Scala").
        Compiler("Java", "JVM", "Java").
        Compiler("Rust", "x64", "Rust").
        Compiler("Rust", "x86", "Rust").
        Compiler("Rust", "WASM", "Rust").
        Compiler("Scala", "JVM", "Scala").
        Compiler("Scala", "JavaScript", "Scala").

        // Bootstrap compilers.
        Compiler("C", "x86", "x86").
        Compiler("OCaml", "x86", "C").
        Compiler("Java", "JVM", "C").
        Compiler("Scala", "JVM", "Pizza").
        Compiler("Pizza", "JVM", "Java").
        Compiler("Rust", "x86", "OCaml").
    };
    let rules = #{
        Runnable(language) :- Machine(language).
        Runnable(language) :- Compiler(language, to, written_in), Runnable(to), Runnable(written_in).
        Runnable(language) :- Interpreter(language, written_in), Runnable(written_in).

        SourceToTarget(source, target) :- Compiler(source, target, written_in), Runnable(written_in).

        RunnableOnWeb(language) :- SourceToTarget(language, "WASM").
        RunnableOnWeb(language) :- SourceToTarget(language, "JavaScript").
        RunnableOnWeb(language) :- SourceToTarget(language, mid), RunnableOnWeb(mid).
        CompilableOnWeb(language) :- Compiler(language, _, written_in), RunnableOnWeb(written_in).
    };
    println("Runnable languages:");
    query facts, rules select language from Runnable(language) |> println;
    println("What source languages can compile to what target languages?");
    query facts, rules select (source, target) from SourceToTarget(source, target) |> println;
    println("Can we run the Flix compiler on the web (i.e., JavaScript or WASM)?");
    not Vector.isEmpty(query facts, rules select true from CompilableOnWeb("Flix")) |> println;
    println("Can we run Flix programs on the web (i.e., JavaScript or WASM)?");
    not Vector.isEmpty(query facts, rules select true from RunnableOnWeb("Flix")) |> println

def ex1_14(): Unit \ IO = 
    let facts = #{
        Person("Child1").
        Person("Parent1").
        Parent("Child1", "Parent1").
    };
    let broken = #{
        Orphan(c) :- Person(c), Person(p), not Parent(c, p).
    };
    "Broken rules:" |> println;
    query facts, broken select c from Orphan(c) |> println;
    "Fixed rules:" |> println;
    let fixed = #{
        HasParent(c) :- Parent(c, _).
        Orphan(c) :- Person(c), not HasParent(c).
    };
    query facts, fixed select c from Orphan(c) |> println

def ex1_17(): Unit \ IO = 
    let facts = #{
        Movie("Reservoir Dogs", "Action").
        Movie("Pulp Fiction", "Action").
        Movie("Apocalypse Now", "War").
        Movie("The Godfather", "Crime").

        StarringIn("Reservoir Dogs", "Steve Buscemi").
        StarringIn("Reservoir Dogs", "Michael Madsen").
        StarringIn("Reservoir Dogs", "Harvey Keitel").
        StarringIn("Reservoir Dogs", "Quentin Tarantino").

        StarringIn("Pulp Fiction", "John Travolta").
        StarringIn("Pulp Fiction", "Samuel L. Jackson").
        StarringIn("Pulp Fiction", "Uma Thurman").
        StarringIn("Pulp Fiction", "Bruce Willis").
        StarringIn("Pulp Fiction", "Quentin Tarantino").

        StarringIn("Apocalypse Now", "Martin Sheen").
        StarringIn("Apocalypse Now", "Marlon Brando").
        StarringIn("Apocalypse Now", "Francis Ford Coppola").

        StarringIn("The Godfather", "Al Pacino").
        StarringIn("The Godfather", "Marlon Brando").
        StarringIn("The Godfather", "Robert de Niro").

        DirectedBy("Reservoir Dogs", "Quentin Tarantino").
        DirectedBy("Pulp Fiction", "Quentin Tarantino").
        DirectedBy("Apocalypse Now", "Francis Ford Coppola").
        DirectedBy("The Godfather", "Francis Ford Coppola").
    };
    let rules = #{
        DirectorAppearsIn(movie) :- Movie(movie, _), DirectedBy(movie, director), StarringIn(movie, director).
        DirectorDoesNotAppearIn(movie) :- Movie(movie, _), not DirectorAppearsIn(movie).
        DoesNotAppearInAll(director) :- DirectedBy(movie, director), DirectorDoesNotAppearIn(movie).
        AppearsInAll(director) :-  DirectedBy(movie, director), Movie(movie, _), not DoesNotAppearInAll(director).
    };
    "Movies the director appears in:" |> println;
    query facts, rules select movie from DirectorAppearsIn(movie) |> println;
    "\nMovies the director does not appear in:" |> println;
    query facts, rules select movie from DirectorDoesNotAppearIn(movie) |> println;
    "\nDirectors that appear in all their movies:" |> println;
    query facts, rules select director from AppearsInAll(director) |> println

def ex1_18(): Unit \ IO =
    let facts = #{
        // Runescape bars and beers
        Drinks("Alice", "Asgarnian Ale").
        Drinks("Alice", "Dragon Bitter").
        Drinks("Bob", "Greenman's Ale").
        Drinks("Charlie", "Dwarven Stout").

        Frequents("Alice", "Blue Moon Inn").
        Frequents("Bob", "Jolly Boar Inn").
        Frequents("Charlie", "Rising Sun Inn").

        Serves("Blue Moon Inn", "Asgarnian Ale").
        Serves("Blue Moon Inn", "Dragon Bitter").
        Serves("Jolly Boar Inn", "Greenman's Ale").
        Serves("Jolly Boar Inn", "Dwarven Stout").
        Serves("Rising Sun Inn", "Wizard's Mind Bomb").
        Serves("Rising Sun Inn", "Asgarnian Ale").
    };
    /*
        LikesBeer(person, beer) :- Drinks(person, beer).
        ServesBeer(bar, beer) :- Serves(bar, beer).
        FrequentsBar(person, bar) :- Frequents(person, bar).
        DislikesBar(person, bar) :- FrequentsBar(person, bar), ServesBeer(bar, beer), not LikesBeer(person, beer).
    */
    let rules = #{
        FrequentsBarLike(person) :- Drinks(person, beer), Frequents(person, bar), Serves(bar, beer).

        // Assume a person dislikes a drink if there is no Drinks fact containing the drink and person
        FrequentsBarSomeDislike(person) :- Drinks(person, _), Frequents(person, bar), Serves(bar, beer), not Drinks(person, beer). 
        FrequentsBarOnlyDislike(person) :- Drinks(person, beer), Frequents(person, bar), not Serves(bar, beer). 

    };
    "Persons that frequent some bar that serves a beer they like:" |> println;
    query facts, rules select person from FrequentsBarLike(person) |> println;
    "\nPersons that frequent some bar that serves some beer they dont like:" |> println;
    query facts, rules select person from FrequentsBarSomeDislike(person) |> println;
    "\nPersons that frequent some bar that serves only beers they dislike:" |> println;
    query facts, rules select person from FrequentsBarOnlyDislike(person) |> println



def query1(c: List[(Int32, String)], 
           o: List[(Int32, Int32, String)], 
           p: List[(Int32, String, Int32)]): List[(String, String, String)] = 
    let rules = #{
        Result(customerName, orderDate, productName) :-
            Order(orderId, customerId, orderDate),
            Customer(customerId, customerName),
            Product(orderId, productName, productPrice), if (productPrice > 10).
    };
    let customers = inject c into Customer;
    let orders = inject o into Order;
    let products = inject p into Product;
    query customers, orders, products, rules select (customerName, orderDate, productName) from Result(customerName, orderDate, productName) |> Vector.toList

def ex2_01(): Unit \ IO = 
    let c = ((1, "Alice") :: (2, "Bob") :: (3, "Charlie") :: Nil);
    let o = ((1, 1, "2024-09-16") :: (2, 2, "2024-09-15") :: (3, 3, "2024-09-14") :: Nil);
    let p = ((1, "Apple", 5) :: (2, "Banana", 15) :: (3, "Strawberry", 25) :: Nil);
    query1(c, o, p) |> println

def ex2_03(): Unit \ IO = 
    let facts = #{
        StarsWith("Tom Hanks", "Kevin Bacon").
        StarsWith("Tom Hanks", "Robin Wright").
        StarsWith("Ed Harris", "Kevin Bacon").
        StarsWith("Ed Harris", "Tom Hanks").
        StarsWith("Robin Wright", "Tom Hanks").
        BaconNumber("Kevin Bacon"; Down.Down(0)).
    };
    let rules = #{
        StarsWith(actor1, actor2) :- StarsWith(actor2, actor1).
        BaconNumber(actor; n + Down.Down(1)) :- StarsWith(actor, actor2), BaconNumber(actor2; n). // fix senere
    };
    query facts, rules select (actor, n) from BaconNumber(actor; n) |> println


def latticeTest(): Unit \ IO = 
    println("Starting");
    let func = () -> {
        let start = Clock.currentTime(TimeUnit.Seconds);
        let map = List.map(x -> (x, x + 1), List.range(1, 200));
        let injected = inject map into Edge;
        let path = injected <+> #{
            Path(x, y; Down.Down(1)) :- Edge(x, y).
            Path(x, y; n + Down.Down(1)) :- Path(x, z; n), Edge(z, y).
        };
        let r = query path select (x, y, set) from Path(x,y; set);
        let x = Vector.head(r);
        if(Option.isEmpty(x)) {
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
        let injected = inject map into Edge;
        let path = injected <+> #{
            Edge(x, y) :- Edge(y, x).
            Path(x, y) :- Edge(x, y).
            Path(x, y) :- Path(x, z), Edge(z, y).
        };
        let r = query path select (x, y) from Path(x,y);
        let x = Vector.head(r);
        if(Option.isEmpty(x)) {
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
    if(num <= 0) {
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
    if(x < 2) false
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

pub def pathh(): Unit \ IO = Clock.runWithIO(() ->{
    let now = Clock.now();
    let edges = List.range(0, 5000) |> List.map(i -> (i, i+1));
    let f = inject edges into Edge;
    let r = #{
        A(1).
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Path(x, y), Edge(y, z).
        // DumbRule(1,2,3) :- Path(x, 1), A(x).
    };
    query f, r select (x, y) from Path(x, y) |> Vector.head |> println;
    let elapsed = Clock.now() - now;
    println(elapsed / 1_000i64)
    })

pub def dumb3333(): Unit \ IO = 
    let r = #{
        A(1).
    };
    query r select x from A(x) |> Vector.head |> println;
    ()

pub def dumb(): Unit \ IO = 
    let aFacts = List.range(0,101);
    let bFacts = List.range(0,10);
    let f1 = inject aFacts into A;
    let f2 = inject bFacts into B;
    let r = #{
        A(x) :- D(x).
        D(x) :- A(x).
        B(x) :- D(x).
        C(x) :- A(x), B(x).
    };
    query f1, f2, r select x from C(x)  |> println;
    ()


pub def dumb2(): Unit \ IO = 
    let aFacts = List.range(0,1000);
    let f1 = inject aFacts into A;
    let r = #{
        C(a, b) :- A(a), A(b).
    };
    query f1, r select x from C(x, _) |> Vector.length  |> println;
    ()

pub def fff(): Unit \ IO = {
    let aFacts = List.range(0,1000);
    aFacts |> List.join(",") |> println
}