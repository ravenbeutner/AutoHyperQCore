(*    
    Copyright (C) 2022-2023 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module AutoHyperQCore.HyperQPTL 

open FsOmegaLib.LTL

open System
open System.IO

open Util

type TraceVariable = String
type PropVariable = String
    
type HyperQPTLQuantifier = 
    | ForallProp of PropVariable
    | ExistsProp of PropVariable
    | ForallTrace of TraceVariable
    | ExistsTrace of TraceVariable

type HyperQPTLAtom<'L> =
    | TraceAtom of 'L * TraceVariable
    | PropAtom of PropVariable

type HyperQPTL<'L when 'L: comparison> = 
    {
        QuantifierPrefix : list<HyperQPTLQuantifier>
        LTLMatrix : LTL<HyperQPTLAtom<'L>>
    }
    
module HyperQPTL =
    let quantifiedTraceVariables (formula : HyperQPTL<'L>) =
        formula.QuantifierPrefix
        |> List.choose (fun x ->
            match x with
            | ForallTrace pi | ExistsTrace pi -> Some pi
            | _ -> None)
        
    let quantifiedPropVariables (formula : HyperQPTL<'L>) =
        formula.QuantifierPrefix
        |> List.choose (fun x ->
            match x with
            | ForallProp p | ExistsProp p -> Some p
            | _ -> None)
    

    let map f (formula : HyperQPTL<'L>)  = 
        {
            QuantifierPrefix = formula.QuantifierPrefix
            LTLMatrix =    
                formula.LTLMatrix 
                |> LTL.map (fun x -> 
                    match x with 
                    | PropAtom q -> PropAtom q 
                    | TraceAtom (x, n) -> TraceAtom (f x, n) 
                )
        }

    let findError (formula : HyperQPTL<'L>) = 
        let propVars = quantifiedPropVariables formula
            
        let traceVars = quantifiedTraceVariables formula

        try 
            if propVars |> set |> Set.count <> List.length propVars then 
                raise <| AnalysisException $"Some propositional variable is used more than once."

            if traceVars |> set |> Set.count <> List.length traceVars then 
                raise <| AnalysisException $"Some trace variable is used more than once."

            LTL.allAtoms formula.LTLMatrix
            |> Set.iter (fun x -> 
                match x with 
                | PropAtom q -> 
                    if List.contains q propVars |> not then 
                        raise <| AnalysisException $"Propositional Variable %s{q} is used but not defined in the prefix"

                | TraceAtom (_, n) -> 
                    if List.contains n traceVars |> not then 
                        raise <| AnalysisException $"Trace Variable %s{n} is used but not defined in the prefix"
                )
            None 
        
        with 
            | AnalysisException msg -> Some msg

    let print (varNames : 'L -> String) (formula : HyperQPTL<'L>) =
        let strWriter = new StringWriter()
        for t in formula.QuantifierPrefix do
            match t with 
            | ForallTrace pi -> strWriter.Write("forall " + string(pi) + ". ")
            | ExistsTrace pi -> strWriter.Write("exists " + string(pi) + ". ")
            | ForallProp p -> strWriter.Write("A " + string(p) + ". ")
            | ExistsProp p -> strWriter.Write("E " + string(p) + ". ")

        let varStringer x =
            match x with
            | TraceAtom (x, pi) -> "\"" + varNames x + "\"_" + string(pi)
            | PropAtom p -> string p
       
        strWriter.Write(LTL.printInSpotFormat varStringer formula.LTLMatrix)
        strWriter.ToString()



module Parser =
    open FParsec
    
    let private keywords =
        [
            "X"
            "G"
            "F"
            "U"
            "W"
            "R"
        ]
        
    let propVarParser : Parser<PropVariable, unit> =
        attempt (
            pipe2
                letter
                (manyChars (letter <|> digit <|> pchar '-' <|> pchar '@'))
                (fun x y -> string(x) + y)
            >>= fun s ->
                if List.contains s keywords then
                    fail ""
                else preturn s
            )
        
    
    let traceVarParser =
        pipe2
            letter
            (manyChars (letter <|> digit <|> pchar '-'))
            (fun x y -> string(x) + y)
            
   
    let hyperQPTLQuantifierPrefixParser =
        let existsTraceParser = 
            skipString "exists " >>. spaces >>. traceVarParser .>> spaces .>> pchar '.'
            |>> fun pi -> ExistsTrace pi

        let forallTraceParser = 
            skipString "forall " >>. spaces >>. traceVarParser .>> spaces .>> pchar '.'
            |>> fun pi -> ForallTrace pi

        let existsPropParser = 
            skipString "E " >>. spaces >>. propVarParser .>> spaces .>> pchar '.'
            |>> fun p -> ExistsProp p

        let forallPropParser = 
            skipString "A " >>. spaces >>. propVarParser .>> spaces .>> pchar '.'
            |>> fun p -> ForallProp p


        spaces >>.
        many1 (choice [existsTraceParser; forallTraceParser; existsPropParser; forallPropParser] .>> spaces)
        .>> spaces


    let private hyperQPTLAtomParser atomParser =
        attempt (
            (atomParser .>> pchar '_' .>>. traceVarParser)
            |>> fun (x, y) -> TraceAtom(x, y)
        )
        <|>
        (propVarParser |>> PropAtom)
        
    let private hyperQPTLParser (atomParser : Parser<'T, unit>) =     
        pipe2 
            hyperQPTLQuantifierPrefixParser
            (FsOmegaLib.LTL.Parser.ltlParser (hyperQPTLAtomParser atomParser))
            (fun x y -> {HyperQPTL.QuantifierPrefix = x; LTLMatrix = y})
    
    let parseHyperQPTL (atomParser : Parser<'T, unit>) s =    
        let full = hyperQPTLParser atomParser .>> spaces .>> eof
        let res = run full s
        match res with
        | Success (res, _, _) -> Result.Ok res
        | Failure (err, _, _) -> Result.Error err

        