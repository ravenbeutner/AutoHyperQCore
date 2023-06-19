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

module AutoHyperQCore.ModelChecking

open System

open FsOmegaLib.LTL
open FsOmegaLib.SAT
open FsOmegaLib.GNBA
open FsOmegaLib.NBA
open FsOmegaLib.Operations

open Util
open SolverConfiguration
open HyperQPTL
open AutomataUtil

type ModelCheckingOptions = 
    {
        ComputeWitnesses : bool // Compute witnesses or counterexamples from outermost quantifiers 
        InitialSystemSimplification : bool
        IntermediateSimplification : bool

        Logger : String -> unit // A Logger that is called with intermediate debug statements
        RaiseExceptions : bool // If set to true, we do not catch and handle inner exceptions
    }

    member this.LoggerN s = 
        this.Logger (s + "\n")

let private constructAutomatonSystemProduct (aut : GNBA<int, HyperQPTLAtom<'L>>) (ts : GNBA<int, 'L>) (index : TraceVariable) (project : bool) =
    let tsGNBA =
        ts
        |> GNBA.mapAPs (fun x -> TraceAtom(x, index))
        
    let newAPs = 
        aut.APs
        |> List.filter (fun x ->
            match x with
            | TraceAtom (_, i) -> i <> index
            | PropAtom _ -> true
        )

    let product =
        (aut, tsGNBA)
        ||> AutomataUtil.constructConjunctionOfGnbaPair 

    if project then
        GNBA.projectToTargetAPs newAPs product 
    else 
        product
    
    
let private projectAwayAP (aut : GNBA<int, HyperQPTLAtom<'L>>) (index : PropVariable) =
    let newAPs = 
        aut.APs
        |> List.filter (fun x ->
            match x with
            | TraceAtom _ -> true
            | PropAtom p -> p <> index
        )
    
    aut
    |> GNBA.projectToTargetAPs newAPs
    
type PossiblyNegatedAutomaton<'L when 'L: comparison> =
    {
        Aut : GNBA<int, HyperQPTLAtom<'L>>
        IsNegated : bool 
    }

/// The trace variables in nonProjectedTraces will remain within the automataon language, i.e., they will not be projected away
let rec private generateAutomatonRec (config : SolverConfiguration) (mcOptions : ModelCheckingOptions) (tsMap : Map<TraceVariable, GNBA<int, 'L>>) (nonProjectedTraces : Set<TraceVariable>) (quantifierPrefix : list<HyperQPTLQuantifier>) (possiblyNegatedAut : PossiblyNegatedAutomaton<'L>) = 
    if quantifierPrefix.IsEmpty then
        possiblyNegatedAut   
    else
        let lastQuantifier = List.last quantifierPrefix

        let remainingPrefix = quantifierPrefix[..quantifierPrefix.Length - 2]

        match lastQuantifier with
        | ExistsTrace pi  -> 
            let sw = System.Diagnostics.Stopwatch()

            mcOptions.LoggerN $"========================= \"exists %s{pi}\" ========================="
            mcOptions.LoggerN $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}, System Size: %i{tsMap.[pi].States.Count}"

            sw.Start()
            let positiveAut = 
                if possiblyNegatedAut.IsNegated then
                    mcOptions.Logger $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AutoHyperQCoreException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        mcOptions.Logger $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AutoHyperQCoreException err
                    else 
                        mcOptions.Logger $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            mcOptions.LoggerN $"Done. | Automaton Size: %i{positiveAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            mcOptions.Logger $"Start automaton-system-product..."
            sw.Restart()
            let nextAut = constructAutomatonSystemProduct positiveAut tsMap.[pi] pi (Set.contains pi nonProjectedTraces |> not)
            mcOptions.LoggerN $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            mcOptions.LoggerN "=================================================="
            mcOptions.LoggerN ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = false}
            
        | ForallTrace pi -> 
            let sw = System.Diagnostics.Stopwatch()

            mcOptions.LoggerN $"========================= \"forall %s{pi}\" ========================="
            mcOptions.LoggerN $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}, System Size: %i{tsMap.[pi].States.Count}"

            sw.Start()
            let negativeAut = 
                if not possiblyNegatedAut.IsNegated then 
                    mcOptions.Logger $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AutoHyperQCoreException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        mcOptions.Logger $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AutoHyperQCoreException err
                    else 
                        mcOptions.Logger $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            mcOptions.LoggerN $"Done. | Automaton Size: %i{negativeAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            mcOptions.Logger $"Start automaton-system-product..."
            sw.Restart()
            let nextAut = constructAutomatonSystemProduct negativeAut tsMap.[pi] pi (Set.contains pi nonProjectedTraces |> not)
            mcOptions.LoggerN $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            mcOptions.LoggerN "=================================================="
            mcOptions.LoggerN ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = true}
        | ExistsProp p ->
            let sw = System.Diagnostics.Stopwatch()

            mcOptions.LoggerN $"========================= \"E %s{p}\" ========================="
            mcOptions.LoggerN $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}"

            sw.Start()
            let positiveAut = 
                if possiblyNegatedAut.IsNegated then
                    mcOptions.Logger $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AutoHyperQCoreException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        mcOptions.Logger $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AutoHyperQCoreException err
                    else 
                        mcOptions.Logger $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            mcOptions.LoggerN $"Done. | Automaton Size: %i{positiveAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"


            mcOptions.Logger $"Start projection..."
            sw.Restart()
            let nextAut = projectAwayAP positiveAut p
            mcOptions.LoggerN $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            mcOptions.LoggerN "=================================================="
            mcOptions.LoggerN ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = false}
            
        | ForallProp p ->
            let sw = System.Diagnostics.Stopwatch()

            mcOptions.LoggerN $"========================= \"A %s{p}\" ========================="
            mcOptions.LoggerN $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}"


            sw.Start()
            let negativeAut = 
                if not possiblyNegatedAut.IsNegated then 
                    mcOptions.Logger $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AutoHyperQCoreException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        mcOptions.Logger $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AutoHyperQCoreException err
                    else 
                        mcOptions.Logger $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            mcOptions.LoggerN $"Done. | Automaton Size: %i{negativeAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            mcOptions.Logger $"Start projection..."
            sw.Restart()
            let nextAut = projectAwayAP negativeAut p
            mcOptions.LoggerN $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            mcOptions.LoggerN "=================================================="
            mcOptions.LoggerN ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = true}


let generateAutomaton (config : SolverConfiguration) (mcOptions: ModelCheckingOptions) (tsmap : Map<TraceVariable, GNBA<int, 'L>>) (nonProjectedTraces: Set<TraceVariable>) (quantifierPrefix : list<HyperQPTLQuantifier>) (formula : LTL<HyperQPTLAtom<'L>>) = 
    let startWithNegated =
        if List.isEmpty quantifierPrefix then 
            false 
        else 
            match List.last quantifierPrefix with
            | ForallTrace _ | ForallProp _ -> true
            | ExistsTrace _ | ExistsProp _ -> false

    let body = 
        if startWithNegated then 
            LTL.Not formula
        else 
            formula

    mcOptions.LoggerN "========================= LTL-to-GNBA ========================="
    mcOptions.Logger $"Start LTL-to-GNBA translation..."
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    let aut =
        match FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetLtl2tgbaPath body with 
        | Success aut -> aut 
        | Fail err -> raise <| AutoHyperQCoreException err 

    mcOptions.LoggerN $"Done. | Automaton Size: %i{aut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

    mcOptions.LoggerN "=================================================="
    mcOptions.LoggerN ""

    generateAutomatonRec config mcOptions tsmap nonProjectedTraces quantifierPrefix {PossiblyNegatedAutomaton.Aut = aut; IsNegated = startWithNegated}
    
let modelCheck (config : SolverConfiguration) mcOptions (tsMap : Map<TraceVariable, GNBA<int, 'L>>) (hyperqptl : HyperQPTL<'L>) =
    let tsMapSimplified = 
        tsMap
        |> Map.map (fun pi gnba -> 
            if mcOptions.InitialSystemSimplification then 
                // We pass the gnba to spot to enable easy preprocessing 

                mcOptions.LoggerN $"========================= System Simplification for \"%s{pi}\" ========================="
                mcOptions.LoggerN $"Old Size: %i{gnba.Skeleton.States.Count}"
                mcOptions.Logger $"Start GNBA simplification..."
                
                let sw = System.Diagnostics.Stopwatch()
                sw.Start()

                let gnba' = 
                    match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath (Effort.HIGH) gnba with
                    | Success x -> x
                    | Fail err -> raise <| AutoHyperQCoreException err

                mcOptions.LoggerN $"Done. | New Size: %i{gnba'.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

                mcOptions.LoggerN "=================================================="
                mcOptions.LoggerN ""

                gnba'
            else 
                gnba
            )

    // We determine which traces we do not project away to compute witnesses 
    // This is the largest prefix of the same qunatfier-type of the prefix 
    let nonProjectedTraces : Set<TraceVariable> = 
        if mcOptions.ComputeWitnesses |> not then 
            Set.empty
        else 
            let l =
                hyperqptl.QuantifierPrefix
                |> List.choose (function 
                    | ForallProp _ | ExistsProp _ -> None 
                    | ForallTrace pi -> Some (true, pi)
                    | ExistsTrace pi -> Some (false, pi)
                    )

            assert (List.isEmpty l |> not)

            // Find the first index that differs from the quantifiertype of the first variable (head of l)
            let a = 
                l 
                |> List.tryFindIndex (fun (y: bool * TraceVariable) -> fst y <> fst (List.head l))
                |> Option.defaultValue (List.length l)
                |> fun x -> x - 1

            l[..a] 
            |> List.map snd 
            |> set


    let possiblyNegatedAut = generateAutomaton config mcOptions tsMapSimplified nonProjectedTraces hyperqptl.QuantifierPrefix hyperqptl.LTLMatrix
    let aut = possiblyNegatedAut.Aut
    let isNegated = possiblyNegatedAut.IsNegated
   
    assert (mcOptions.ComputeWitnesses || List.isEmpty aut.APs)

    if not mcOptions.ComputeWitnesses then 
        // Just check for emptiness, we use spot for this

        mcOptions.LoggerN "========================= Emptiness Check ========================="
        mcOptions.LoggerN $"Automaton size: %i{aut.Skeleton.States.Count}"
        mcOptions.Logger $"Start emptiness check..."
        let sw = System.Diagnostics.Stopwatch()
        sw.Start()

        let res = 
            match FsOmegaLib.Operations.AutomataChecks.isEmpty mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath aut with
            | Success isEmpty ->
                if isNegated then
                    isEmpty
                else
                    not isEmpty
            | Fail err -> raise <| AutoHyperQCoreException err

        mcOptions.LoggerN $"Done. | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"
        mcOptions.LoggerN "=================================================="
        mcOptions.LoggerN ""


        res, None

    else 
        mcOptions.LoggerN "========================= Emptiness Check / Witness Search ========================="
        mcOptions.Logger $"Automaton size: %i{aut.Skeleton.States.Count}"
        mcOptions.Logger $"Start GNBA-to-NBA translation..."
        let sw = System.Diagnostics.Stopwatch()
        sw.Start()

        let nba = 
            match FsOmegaLib.Operations.AutomatonConversions.convertToNBA mcOptions.RaiseExceptions  config.GetMainPath config.GetAutfiltPath Effort.HIGH aut with
            | Success nba -> nba
            | Fail err -> raise <| AutoHyperQCoreException err

        mcOptions.LoggerN $"Done. | New Size: %i{nba.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

        mcOptions.Logger $"Start lasso search in NBA..."
        sw.Restart()
        let res = AutomataUtil.shortestAcceptingPaths nba

        mcOptions.LoggerN $"Done. | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"
        mcOptions.LoggerN "=================================================="
        mcOptions.LoggerN ""

        match res with 
        | None -> 
            // The automataon is empty 
            (if isNegated then true else false), None 
        | Some lasso -> 

            // We can assume that each NF in this lasso is SAT
            let makeDNFExplict (d : DNF<int>) = 
                // We take the smallest literal for printing
                let f = List.minBy List.length d 

                f 
                |> List.map (fun lit -> 
                    let ap, pi = 
                        match nba.APs.[Literal.getValue lit] with 
                        | PropAtom _ -> raise <| AutoHyperQCoreException $"Encountered a quantified propositional AP in the lasso, should not happen!"
                        | TraceAtom (a, pi) -> a, pi
                    
                    pi, match lit with PL _ -> PL ap | NL _ -> NL ap
                    )

            let modPrefix = lasso.Prefix |> List.map makeDNFExplict 
            let modLoop = lasso.Loop |> List.map makeDNFExplict 

            let witnessPerTraceVariableMap = 
                nonProjectedTraces 
                |> Set.toList
                |> List.map (fun pi -> 
                    let prefix = 
                        modPrefix 
                        |> List.map (fun clause -> 
                            clause
                            |> List.filter (fun (pi', _) -> pi = pi')
                            |> List.map snd
                            )

                    let loop = 
                        modLoop 
                        |> List.map (fun clause -> 
                            clause
                            |> List.filter (fun (pi', _) -> pi = pi')
                            |> List.map snd
                            )

                    pi, 
                    {
                        Lasso.Prefix = prefix
                        Loop = loop
                    }
                    )
                |> Map.ofList

            // The automaton is non-empty
            (if isNegated then false else true), (Some witnessPerTraceVariableMap) 