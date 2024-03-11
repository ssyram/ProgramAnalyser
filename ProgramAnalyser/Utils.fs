module ProgramAnalyser.Utils

open System.IO
open Newtonsoft.Json
open System.Collections
open System.Collections.Generic
open System.Security.Cryptography
open System.Text
open FSharp.Text.Lexing
open Global
open MathNet.Numerics.Distributions
open Microsoft.FSharp.Reflection

let inline uncurry f (a, b) = f a b
let inline ($) f x = f x

module BiMap = begin
    let fstMap f (a, b) = (f a, b)
    let sndMap f (a, b) = (a, f b)
    let pairMap (f1, f2) (a, b) = (f1 a, f2 b)
    let bothMap f (a, b) = (f a, f b)
end

let undefined _ = failwith "UNDEFINED"
let (++) = List.append
let IMPOSSIBLE _ = failwith "IMPOSSIBLE"
let inline flip f a b = f b a
let inline toString x = $"{x}"

type IUnwrappable<'inner> =
    abstract member Unwrap : unit -> 'inner

let inline unwrap (v : #IUnwrappable<_>) = v.Unwrap ()

let println str = printfn $"{str}"

/// a more general version of `extract` that does not require `unwrap`
/// but it does not enjoy type safety -- the extract type depends on the requirement
let inline extract (v : 'a) : 'b =
    let _, args = FSharpValue.GetUnionFields(v, typeof<'a>) in
    match args with
    | [| x |] -> x :?> 'b
    | arr ->
        let tupleType = typedefof<'b> in
        let ctors = tupleType.GetConstructors() in

        if ctors.Length <> 1 then
            failwith "Target type 'b must be a tuple";
        
        let ctor = ctors[0] in
        let ctorParams = ctor.GetParameters() in

        if ctorParams.Length <> arr.Length then
            failwith "Array and tuple lengths do not match";

        ctor.Invoke(args) :?> 'b

let getPrecision (wrt : Numeric) hint num =
    let num = abs num in
    if num = NUMERIC_ZERO then 0 else
    let num = num * pown wrt (-hint) in
    let rec upFind precision num =
        if num >= NUMERIC_ONE then (precision, num)
        else upFind (precision - 1) (num * wrt) in
    let rec downFind precision num =
        if num < wrt then (precision, num)
        else downFind (precision + 1) (num / wrt) in
    downFind hint num
    |> uncurry upFind
    |> fst

let foldWith lst init func =
    let mutable ret = init in begin
    for e in lst do ret <- func e ret done; 
    ret end

type HashTableEnumerator<'k, 'v>(data : IEnumerator) =
    interface IEnumerator<'k * 'v> with
        member this.Current =
            let entry = data.Current :?> DictionaryEntry in
            (entry.Key :?> 'k, entry.Value :?> 'v)
        member this.MoveNext() = data.MoveNext ()
        member this.Reset() = data.Reset ()
        member this.Current = data.Current
        member this.Dispose() = ()

/// a type-safe wrapper for Hashtable 
type HashMap<'k, 'v>(data : Hashtable) =
    class
        new () = new HashMap<'k, 'v>(Hashtable ())
        member x.size = data.Count
        member x.add (key : 'k) (value : 'v) = data[key] <- value
//            data.Add (key, value)
        member x.Item (key : 'k) = Option.get $ x.tryFind key
        member x.tryFind (key : 'k) =
            let v = data[key] in
            if v = null then None else Some (v :?> 'v)
        member x.remove (key : 'k) = data.Remove key
        member x.isEmpty () = data.Count = 0
        
        interface IEnumerable<'k * 'v> with
            member this.GetEnumerator(): IEnumerator<'k * 'v> =
                new HashTableEnumerator<'k, 'v>(data.GetEnumerator ())
            member this.GetEnumerator(): IEnumerator = data.GetEnumerator ()
    end
    

let forEach lst func =
    foldWith lst () $ fun a () -> func a 
    
module HashMap = begin
    let tryFind k (map : HashMap<'k, 'v>) = map.tryFind k
    let fromSeq (s : seq<'k * 'v>) =
        let ret = new HashMap<'k, 'v> () in
        foldWith s () $ fun (k, v) () -> ret.add k v
        ret
    let fromMap map = fromSeq $ Map.toSeq map
    /// can re-map
    let add k v (map : HashMap<'k, 'v>) = map.add k v
    let union lst (map : HashMap<'k, 'v>) =
        foldWith lst () $ fun (k, v) () -> map.add k v 
    let inline size (map : HashMap<'k, 'v>) = map.size
    let containsKey k (map : HashMap<'k, 'v>) = match map.tryFind k with None -> false | Some _ -> true 
    let compute k f (map : HashMap<'k, 'v>) = match f $ map.tryFind k with
                                              | Some v -> map.add k v
                                              | None -> map.remove k
    let find k (map : HashMap<'k, 'v>) = Option.get $ map.tryFind k
    let isEmpty (map : HashMap<'k, 'v>) = map.isEmpty ()
    let filter pred (map : HashMap<'k, 'v>) =
        let nMap = Hashtable () in
        foldWith map () $ fun (k, v) () -> if pred k v then nMap.Add (k, v); 
        new HashMap<'k, 'v>(nMap)
    let map (f : 'a -> 'b) (map : HashMap<'k, 'a>) = let nMap = Hashtable () in
                                                     foldWith map () $ fun (k, v) () -> nMap.Add (k, f v);
                                                     new HashMap<'k, 'b>(nMap)
    let mapWithKey (f : 'k -> 'v -> 'v) (map : HashMap<'k, 'v>) = 
        let nMap = Hashtable () in
        forEach map $ fun (k, v) -> nMap.Add (k, f k v);
        new HashMap<'k, 'v>(nMap)
    let foldl f init (map : HashMap<'k, 'v>) = foldWith map init $ flip f
end


/// representing the intention of collecting values
/// every value can be collected (set) only once
/// for multiple-time set, use `Cell` instead
type Collect<'t> () =
    let mutable content : 't option = None
    member x.Collected = Option.isSome content
    member x.Value
        with get () =
            match content with
            | Some c -> c
            | None   -> failwith "Variable Not Yet Collected."
        and  set info =
            match content with
            | Some _ -> failwith "Variable has already collected."
            | None   -> content <- Some info
    override x.ToString () = toString content

type 't collect = Collect<'t>

/// create a blank collect type as placeholder
/// a synonym of the default constructor `Collect ()`
let blank () = Collect ()
            
module Collect = begin
    let get (v : _ collect) = v.Value
    let set (c : _ collect) v = c.Value <- v
    let hasValue (c : _ collect) = c.Collected
    let hasCollected (c : _ collect) = c.Collected
    let collected (v : _ collect) = v.Collected
    let optionGet (c : _ collect) = if c.Collected then Some c.Value else None
    /// create a blank collect type as placeholder
    /// a synonym of the default constructor `Collect ()`
    let blank () = Collect ()
    let collect v = let ret = blank () in ret.Value <- v; ret
end

/// the module to normalise an essentially polynomial type
/// that is, to the form: c + \sum_i c_i * \prod_j v_{i, j}
module NormPolynomial = begin
    type ExprEnv<'v> =
        | EEPlus of ExprEnv<'v> list
        | EEMul of ExprEnv<'v> list
        | EEConst of Numeric
        | EEVar of 'v
    /// every element of this type is bound to have shape:
    /// \sum_i c_i * v_ij
    /// where `c_i` is Non-Zero and for every `i`, the set of `v_ij` is unique
    type NormalisedExpr<'v> when 'v : comparison =
        /// the type: var and its counts with the constant at its head
        | NormalisedExpr of Map<Map<'v, uint>, Numeric>
        
    let private (|->) vars c = Map.add vars c Map.empty
    
    let sumNormalisedExprs lst =
        let folder (NormalisedExpr map) (NormalisedExpr toAdd) =
            let folder map (vars, c) =
                match Map.tryFind vars map with
                | Some oc ->
                    if oc + c = NUMERIC_ONE then Map.remove vars map
                    else Map.add vars (oc + c) map
                | None -> Map.add vars c map
            in
            Map.toSeq toAdd
            |> Seq.fold folder map
            |> NormalisedExpr
        in
        Seq.fold folder (NormalisedExpr Map.empty) lst
    let distributeNormalisedExpr (NormalisedExpr l1) (NormalisedExpr l2) =
        Seq.allPairs (Map.toSeq l1) (Map.toSeq l2)
        |> Seq.map (fun ((vars1, const1), (vars2, const2)) ->
            let folder varMap var count =
                match Map.tryFind var varMap with
                | Some oc ->
                    if oc + count = 0u then Map.remove var varMap
                    else Map.add var (oc + count) varMap
                | None -> Map.add var count varMap
            in
            Map.fold folder vars1 vars2 |-> const1 * const2)
        |> Seq.map NormalisedExpr
        |> sumNormalisedExprs
        
    /// guarantee the uniqueness of set `V_j` given `i`, but the order of `i` is not guaranteed
    let rec normaliseExprEnv env =
        match env with
        | EEConst c  -> NormalisedExpr (if c = NUMERIC_ZERO then Map.empty else Map.empty |-> c)  // {} |-> c
        | EEVar v    -> NormalisedExpr ((v |-> 1u) |-> NUMERIC_ONE)  // {v} |-> 1
        | EEPlus lst -> sumNormalisedExprs $ List.map normaliseExprEnv lst
        | EEMul lst  -> List.fold
                            distributeNormalisedExpr
                            (NormalisedExpr (Map.empty |-> NUMERIC_ONE))
                            (List.map normaliseExprEnv lst)
        
    let inline fromNormalisedExpr< ^t, 'v when ^t: (static member FromNormalisedExpr: NormalisedExpr<'v> -> ^t)> env =
        (^t : (static member FromNormalisedExpr : NormalisedExpr<'v> -> ^t) env)
    let inline toExprEnv< ^t, 'v when ^t: (static member ToExprEnv: ^t -> ExprEnv<'v>)> obj =
        (^t : (static member ToExprEnv : ^t -> ExprEnv<'v>) obj)
    let inline normalise< ^t, 'v when
        'v: comparison and 
        ^t: (static member FromNormalisedExpr: NormalisedExpr<'v> -> ^t) and
        ^t: (static member ToExprEnv: ^t -> ExprEnv<'v>)> (obj : ^t) : ^t =
        toExprEnv obj
        |> normaliseExprEnv
        |> fromNormalisedExpr
end

let swap (a, b) = (b, a)
let curry f a b = f (a, b)

let constFunc a = fun _ -> a

let parse tokeniser parser str =
    let tokenStream = LexBuffer<char>.FromString str in
    try parser tokeniser tokenStream
    with
    | e ->
        let lexbuf = tokenStream in
        let errMsg =
            $"Unexpected Token: \"{System.String(lexbuf.Lexeme)}\". At line {lexbuf.StartPos.Line + 1}, " +
            $"column {lexbuf.StartPos.Column}."
        in
        eprintfn $"{errMsg}"
        reraise ()
    
/// Given a string and a list of components to check
/// judge whether the string is composed by the components
///
/// For example:
///     [
///         [ "-" ]
///         [ "no"; "non" ]
///         [ "-"; "_" ]
///         [ "truncation"; "truncate" ]
///     ]
/// may compose:
///     "-non-truncate"
let strConsistsBy str lst =
    let rec loop (rest : string) restLst =
        match restLst with
        | [] -> rest = ""
        | lst :: restLst ->
            let rec internalLoop (lst : string list) =
                match lst with
                | [] -> false
                | e :: lst ->
                    (rest.StartsWith e &&
                     loop rest[e.Length..] restLst) ||
                    internalLoop lst
            in
            internalLoop lst
    in
    loop str lst

let findNormalPdfIntRange mean stdDev threshold =
    let normalPdf = Normal(mean, stdDev) in
    let normalPdf x = normalPdf.Density x in
    let rec findDis distance =
        if normalPdf (mean + distance) < threshold then distance
        else findDis (distance + 1.)
    in
    let distance = findDis 0 in
    int (mean - distance), int (mean + distance)

type AutoIdxMap<'a>() =
    let mutable nextIdx = 0
    
    let content = HashMap<'a, int> ()
    
    let lookUp obj =
        match HashMap.tryFind obj content with
        | Some idx -> idx
        | None ->
            HashMap.add obj nextIdx content;
            nextIdx <- nextIdx + 1;
            nextIdx - 1
            
    member x.LookUp obj = lookUp obj
    
    member x.GetRaw = content

/// take the list until the `pred` returns the first `false`
/// returns also whether the procedure is getting interrupted by `false` or it is a full traversal
/// Return: (list until the first `false`, interrupted)
/// 
/// This information can be used also as the `forall` test
/// that, if it is NOT interrupted, then the `forall` test is TRUE 
let until pred lst =
    let mutable ret = [] in
    let mutable interrupted = false in
    let rec loop lst =
        match lst with
        | [] -> ()
        | e :: lst -> if not $ pred e then interrupted <- true; ()
                      else ret <- e :: ret; loop lst
    in
    loop lst;
    List.rev ret, interrupted

let rec enumEveryN n lst =
    if n = 0 then [ [] ] else
    let len = List.length lst in
    if len < n then []
    elif len = n then [ lst ]
    else match lst with
         | [] -> IMPOSSIBLE ()
         | hd :: lst ->
             let rest = enumEveryN (n - 1) lst in
             let startWithHd = List.map (curry List.Cons hd) rest in
             startWithHd ++ enumEveryN n lst

/// decompose a NON-EMPTY list into its head and the rest of the list
let decomposeList l =
    match l with
    | [] -> failwith "Cannot decompose empty list into head and the rest of the list."
    | hd :: tl -> hd, tl

/// to combine the elements from each list
/// if one of the list is empty, the whole returns empty
let rec listCartesian lst =
    match lst with
    | [] -> []
    | [ x ] -> List.map List.singleton x
    | hLst :: rest ->
        listCartesian rest
        |> List.allPairs hLst
        |> List.map List.Cons

/// to combine the elements from each list
/// if a list is empty, then, it is assumed to have a default element `None`
/// while other elements are all marked `Some`
let rec listMayCartesian lst =
    match lst with
    | [] -> []
    | [ x ] ->
        match x with
        | [] -> [ [ None ] ]
        | x  -> List.map (Some >> List.singleton) x
    | hLst :: rest ->
        let hLst =
            match hLst with
            | [] -> [ None ]
            | hLst -> List.map Some hLst
        in
        listMayCartesian rest
        |> List.allPairs hLst
        |> List.map List.Cons

let encryptStringToBytes_Aes (plainText: string, key: byte[], iv: byte[]) : byte[] =
    use aesAlg = Aes.Create() in
    aesAlg.Key <- key;
    aesAlg.IV <- iv;
    let encryptor = aesAlg.CreateEncryptor(aesAlg.Key, aesAlg.IV) in
    use msEncrypt = new MemoryStream() in
    let csEncrypt = new CryptoStream(msEncrypt, encryptor, CryptoStreamMode.Write) in
    let swEncrypt = new StreamWriter(csEncrypt) in
    swEncrypt.Write(plainText);
    swEncrypt.Close();
    csEncrypt.Close();
    msEncrypt.ToArray()

let encryptFiles
        (filePaths : string list)
        (encryptionInfoFilePath : string)
        (outPath : string) : unit =
    let readContents path = File.ReadAllText(path) in
    let namesAndContents =
        filePaths
        |> List.map (fun path -> Path.GetFileNameWithoutExtension(path), readContents(path)) in
    let jsonString = JsonConvert.SerializeObject(namesAndContents) in

    // Generate a random key and IV for AES encryption
    let aes = Aes.Create() in
    let key = aes.Key in
    let iv = aes.IV in
    let encrypted = encryptStringToBytes_Aes(jsonString, key, iv) in
    File.WriteAllBytes(outPath, encrypted);

    // Save the encryption key and IV
    let encryptionInfo = JsonConvert.SerializeObject((key, iv)) in
    File.WriteAllText(encryptionInfoFilePath, encryptionInfo)

let decryptStringFromBytes_Aes (cipherText: byte[], key: byte[], iv: byte[]) : string =
    use aesAlg = Aes.Create() in
    aesAlg.Key <- key;
    aesAlg.IV <- iv;
    let decryptor = aesAlg.CreateDecryptor(aesAlg.Key, aesAlg.IV) in
    use msDecrypt = new MemoryStream(cipherText) in
    use csDecrypt = new CryptoStream(msDecrypt, decryptor, CryptoStreamMode.Read) in
    use srDecrypt = new StreamReader(csDecrypt) in
    srDecrypt.ReadToEnd()

let decryptAll 
        (encryptionInfoFilePath : string)
        (encryptedFilePath : string)
        : (string * string) list =
    let encrypted = File.ReadAllBytes(encryptedFilePath) in
    let encryptionInfoJson = File.ReadAllText(encryptionInfoFilePath) in
    let (key, iv) = JsonConvert.DeserializeObject<byte[]*byte[]>(encryptionInfoJson) in

    let decryptedJson = decryptStringFromBytes_Aes(encrypted, key, iv) in
    JsonConvert.DeserializeObject<(string*string) list>(decryptedJson) 

let decryptForFiles
        (names : string list)
        (encryptionInfoFilePath : string)
        (encryptedFilePath : string)
        : (string * string) list =
    let names = Set.ofList names in
    let allFiles = decryptAll encryptionInfoFilePath encryptedFilePath in
    allFiles |> List.filter (fun (name, _) -> Set.contains name names)


// let testEncrypt () =
//     let filePath = "../../../../paper-examples/Table 3 (fix add-uniform & random-walk)/parser-inputs3/cav-example-5-Q1.program" in
//     encryptFiles
//         [ filePath ]
//         "../../../../enc.txt"
//         "../../../../int.fl"
//         
// let testDecrypt () =
//     decryptForFiles
//         [ "cav-example-5-Q1.program" ]
//         "../../../../enc.txt"
//         "../../../../int.fl"
//     |> List.iter println

let encryptRequired () =
    let enc, intFl = Flags.ENC_PATHS in
    let dirPath = "../../../../enc" in
    let paths = Seq.toList $ Directory.EnumerateFiles(dirPath, "*", SearchOption.AllDirectories) in
    encryptFiles paths enc intFl;
    println "Enc Done."

let getDecFile name =
    let enc, intFl = Flags.ENC_PATHS in
    let allNames () =
        decryptAll enc intFl
        |> List.map fst
        |> List.map (fun x -> $"\"{x}\"")
        |> String.concat ", "
    match decryptForFiles [ name ] enc intFl with
    | [ (_, content) ] -> content
    | []               -> failwith $ $"Name \"{name}\" not found, all names: " + allNames ()
    | _                -> IMPOSSIBLE ()

let testGetDecFile () =
    List.iter (println << getDecFile) [
        "cav-ex5-config-loop-Q1"
    ]
