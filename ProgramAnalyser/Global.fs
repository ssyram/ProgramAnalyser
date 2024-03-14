module ProgramAnalyser.Global

open System
open Rationals
open System.Numerics


type ILispPrintable =
    abstract member LispPrint : unit -> string

let lispPrint (x : #ILispPrintable) = x.LispPrint ()

[<Struct>]
[<CustomComparison>]
[<CustomEquality>]
type Numeric =
    val private r : Rational
    
    static member ZERO_TOLERANT : Numeric = Numeric (Rational (BigInteger 1, BigInteger 1e50))
    static member ZERO = Numeric Rational.Zero
    static member ONE = Numeric Rational.One
    static member private DOUBLE_ZERO_TOLERANT = double (Numeric.ZERO_TOLERANT.getR ())
    new (i : uint64) = Numeric (Rational (BigInteger i))
    new (i : int) = Numeric (Rational (BigInteger i))
    new (f : float) = Numeric (Rational.Approximate(f, Numeric.DOUBLE_ZERO_TOLERANT))
    new (nr : Rational) = { r = nr }
    member private x.getR () = x.r
    member x.getDouble () = double x.r
    static member Abs (x : Numeric) = Numeric (abs x.r)
    static member RoundUp (n : Numeric) =
        if (n.getR ()).Denominator.GetBitLength () > int64 64 then
            Numeric (Rational.Approximate (double (n.getR ()), Numeric.DOUBLE_ZERO_TOLERANT))
        else n
    static member Parse s =
        try
            Numeric (Rational.ParseDecimal s)
        with
        | _ -> Numeric (Rational.Parse s)
    // override this method to compare any number
    // for example, if the numeric inner-type is double, there should be tolerant range of comparison 
    override x.Equals obj =
        match obj with
        | :? Numeric as nt -> x.r.Equals (nt.getR ())
        | _ -> x.r.Equals obj
    override x.GetHashCode () = x.r.GetHashCode ()
    interface IEquatable<Numeric> with
        member x.Equals(other) = x.Equals other
    interface IFormattable with
        member x.ToString(format, formatProvider) = x.r.ToString(format, formatProvider)
    interface IComparable with
        member x.CompareTo(obj) =
            match obj with
            | :? Numeric as nt -> x.r.CompareTo (nt.getR ())
            | _ -> x.r.CompareTo obj
    static member get_Zero () = Numeric.ZERO
    static member get_One () = Numeric.ONE
    static member Pow (n : Numeric, i : int) =
        Numeric (Rational.Pow (n.getR (), i))
    static member Pow (n : Numeric, i : Numeric) =
        Numeric (Rational.Pow (n.getR (), int (i.getR ())))
    static member ToInt (n : Numeric) =
        int (n.getR ())
    static member ToDouble (n : Numeric) =
        double (n.getR ())
    static member (+) (i : int, r : Numeric) =
        (Numeric i) + r
    static member (+) (r : Numeric, i : int) =
        r + (Numeric i)
    static member (-) (i : int, r : Numeric) =
        (Numeric i) - r
    static member (-) (r : Numeric, i : int) =
        r - (Numeric i)
    static member (*) (i : int, r : Numeric) =
        (Numeric i) * r
    static member (*) (r : Numeric, i : int) =
        r * (Numeric i)
    static member (/) (i : int, r : Numeric) =
        (Numeric i) / r
    static member (/) (r : Numeric, i : int) =
        r / (Numeric i)
    static member (+) (r1 : Numeric, r2 : Numeric) : Numeric =
        Numeric (r1.getR () + r2.getR ()).CanonicalForm
    static member (*) (r1 : Numeric, r2 : Numeric) : Numeric =
        Numeric (r1.getR () * r2.getR ()).CanonicalForm
    static member (-) (r1 : Numeric, r2 : Numeric) : Numeric =
        Numeric (r1.getR () - r2.getR ()).CanonicalForm
    static member (/) (r1 : Numeric, r2 : Numeric) : Numeric =
        if r2.getR () = Rational.Zero then
            failwith "Try dividing 0."
        Numeric (r1.getR () / r2.getR ()).CanonicalForm
    static member (~-) (r : Numeric) = Numeric.ZERO - r
    override x.ToString () = x.r.ToString ()
    member x.ToString (s : string) =
        match s.ToLower () with
        | "n30" ->
            $"{x.r} ({double x.r})"
        | "double" | "float" ->
            $"{double x.r}"
        | _ -> x.r.ToString ()

    member x.printInLispForm () =
        let r = x.r.CanonicalForm
        $"(/ {r.Numerator} {r.Denominator})"
    
    interface ILispPrintable with
        member this.LispPrint() = this.printInLispForm ()
        
    /// near equal
    static member (=~=) (r1 : Numeric, r2 : Numeric) =
        (abs (r1.getR () - r2.getR ())) < Numeric.ZERO_TOLERANT.getR ()

let NUMERIC_ZERO = Numeric.ZERO
let NUMERIC_ONE = Numeric Rational.One

module Flags =
    let mutable DEBUG = false
    let DEFAULT_CONFIG_VAR_RANGE = (Numeric 0, Numeric 5)
    let mutable INT_VARS : Set<string> = Set.empty
    let mutable ENC_PATHS = ("../../../../.enc", "../../../../.int.fl")
    
let debugPrint x =
    if Flags.DEBUG then printfn $"{x}"
