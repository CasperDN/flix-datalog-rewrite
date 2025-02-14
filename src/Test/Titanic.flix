mod Titanic {
    import java.lang.System;

    enum Age with Eq, ToString {
        case Known(Float32)
        case Unknown
    }

    instance Order[Age] {

        pub def compare(x: Age, y: Age): Comparison = match (x,y) {
            case (Age.Known(age1), Age.Known(age2)) => 
                if (age1 < age2) Comparison.LessThan 
                else if (age1 > age2) Comparison.GreaterThan 
                else Comparison.EqualTo
            case (Age.Unknown, Age.Known(_)) => Comparison.LessThan
            case (Age.Known(_), Age.Unknown) => Comparison.GreaterThan
            case _ => Comparison.LessThan
        }

    }

    // Passenger: (Id, Survived, Gender, Age, Fare, Class, EmbarkTown)
    def getFacts(): #{ Passenger(Int32, Int32, String, Age, Float32, String, String) | r } \ {IO, Sys} = 
        let path = "${Common.getCwd()}\\dep\\seaborn-data\\titanic.csv";
        let tuples = Common.loadTuplesFromCSV(path, ",");
        let passengers = List.mapWithIndex(i -> x -> match x {
            case surv :: _ :: gender :: age :: _ :: _ :: fare :: _ :: class :: _ :: adult :: _ :: embarkTown :: _ :: _ :: Nil => 
                (   
                    i,
                    if (surv == "1") 1 else 0, 
                    gender,
                    match Float32.fromString(age) {
                        case Some(age_) => Age.Known(age_)
                        case _ => Age.Unknown
                    },
                    match Float32.fromString(fare) {
                        case Some(fare_) => fare_
                        case _ => ???
                    },
                    class,
                    embarkTown
                )
            case _ => ???
        }, List.slice({start = 1}, {end = List.size(tuples)},tuples));
        inject List.take(30, passengers) into Passenger

    pub def titanic(): Int64 \ {IO, Sys} = 
        let f = getFacts();
        let r = #{
            Survivors(embarkTown; Set#{id}) :- Passenger(id, 1, g, a, fare, c, embarkTown).
            NumSurvivors(embarkTown, Set.size(s)) :- fix Survivors(embarkTown; s). 

            Child(id, survived, gender, fare, class, embarkTown) :- 
                Passenger(id, survived, gender, age, fare, class, embarkTown), if (age < Age.Known(18.0f32)).
        };
        let startTime = System.nanoTime();
        let x = query f, r select set from NumSurvivors("Southampton", set);
        let endTime = System.nanoTime();
        println(x);
        endTime - startTime
}