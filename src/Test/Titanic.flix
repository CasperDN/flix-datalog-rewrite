import java.lang.System;
use Common.loadTuplesFromCSV;

enum Age with Eq, Order {
    case Known(Float32)
    case Unknown
}

// instance Order[Age] {

//     pub def compare(x: Age, y: Age): Comparison = match (x,y) {
//         case (Age.Known(age1), Age.Known(age2)) => 
//             if (age1 < age2) Comparison.LessThan 
//             else if (age1 > age2) Comparison.GreaterThan 
//             else Comparison.EqualTo
//         case (Age.Unknown, Age.Known(_)) => Comparison.LessThan
//         case (Age.Known(_), Age.Unknown) => Comparison.GreaterThan
//         case _ => Comparison.LessThan
//     }
// 
// }


enum Class with Eq, Order {
    case First, Second, Third
}

// Passenger: (Survived, Gender, Age, Fare, Class, EmbarkTown)
def getFacts(): #{ Passenger(Bool, String, Age, Float32, Class, String) | r } \ {IO, Sys} = 
    let tuples = loadTuplesFromCSV("${getCwd()}/dep/titanic.csv", ",");
    let passengers = List.map(x -> match x {
        case surv :: _ :: gender :: age :: _ :: _ :: fare :: _ :: class :: _ :: adult :: _ :: embarkTown :: _ :: _ :: Nil => 
            (   
                surv == "1", 
                gender,
                match Float32.fromString(age) {
                    case Some(age_) => Age.Known(age_)
                    case _ => Age.Unknown
                },
                match Float32.fromString(fare) {
                    case Some(fare_) => fare_
                    case _ => ???
                },
                match class {
                    case "First" => Class.First,
                    case "Second" => Class.Second,
                    case "Third" => Class.Third
                    case _ => println("No such class"); ???
                },
                embarkTown
            )
        case _ => ???
    }, tuples);
    inject passengers into Passenger

def titanic(): Int64 \ {IO, Sys} = 
    let f = getFacts();
    let r = #{
        Child(survived, gender, fare, class, embarkTown) :- 
            Passenger(survived, gender, age, fare, class, embarkTown), 
            if (match age {
                case Age.Known(x) => x < 18.0f32
                case _ => false
            }).
    };
    let startTime = System.nanoTime();
    let x = Vector.find(_ -> true, query f, r select true from Child(true, _, _, _, _));
    let endTime = System.nanoTime();
    println(x);
    endTime - startTime