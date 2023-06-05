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

open FsOmegaLib.LTL
open FsOmegaLib.SAT
open FsOmegaLib.GNBA
open FsOmegaLib.NBA
open FsOmegaLib.Operations

open Util
open RunConfiguration
open HyperQPTL
open AutomataUtil

type ModelCheckingOptions = 
    {
        ComputeWitnesses : bool // Compute witnesses or counterexamples from outermost qunatifiers 
        InitialSystemSimplification : bool
        IntermediateSimplification : bool
    }

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

            Util.LOGGERn $"========================= \"exists %s{pi}\" ========================="
            Util.LOGGERn $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}, System Size: %i{tsMap.[pi].States.Count}"

            sw.Start()
            let positiveAut = 
                if possiblyNegatedAut.IsNegated then
                    Util.LOGGER $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AnalysisException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        Util.LOGGER $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AnalysisException err
                    else 
                        Util.LOGGER $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            Util.LOGGERn $"Done. | Automaton Size: %i{positiveAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            Util.LOGGER $"Start automaton-system-product..."
            sw.Restart()
            let nextAut = constructAutomatonSystemProduct positiveAut tsMap.[pi] pi (Set.contains pi nonProjectedTraces |> not)
            Util.LOGGERn $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            Util.LOGGERn "=================================================="
            Util.LOGGERn ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = false}
            
        | ForallTrace pi -> 
            let sw = System.Diagnostics.Stopwatch()

            Util.LOGGERn $"========================= \"forall %s{pi}\" ========================="
            Util.LOGGERn $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}, System Size: %i{tsMap.[pi].States.Count}"

            sw.Start()
            let negativeAut = 
                if not possiblyNegatedAut.IsNegated then 
                    Util.LOGGER $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AnalysisException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        Util.LOGGER $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AnalysisException err
                    else 
                        Util.LOGGER $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            Util.LOGGERn $"Done. | Automaton Size: %i{negativeAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            Util.LOGGER $"Start automaton-system-product..."
            sw.Restart()
            let nextAut = constructAutomatonSystemProduct negativeAut tsMap.[pi] pi (Set.contains pi nonProjectedTraces |> not)
            Util.LOGGERn $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            Util.LOGGERn "=================================================="
            Util.LOGGERn ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = true}
        | ExistsProp p ->
            let sw = System.Diagnostics.Stopwatch()

            Util.LOGGERn $"========================= \"E %s{p}\" ========================="
            Util.LOGGERn $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}"

            sw.Start()
            let positiveAut = 
                if possiblyNegatedAut.IsNegated then
                    Util.LOGGER $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AnalysisException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        Util.LOGGER $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AnalysisException err
                    else 
                        Util.LOGGER $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            Util.LOGGERn $"Done. | Automaton Size: %i{positiveAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"


            Util.LOGGER $"Start projection..."
            sw.Restart()
            let nextAut = projectAwayAP positiveAut p
            Util.LOGGERn $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            Util.LOGGERn "=================================================="
            Util.LOGGERn ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = false}
            
        | ForallProp p ->
            let sw = System.Diagnostics.Stopwatch()

            Util.LOGGERn $"========================= \"A %s{p}\" ========================="
            Util.LOGGERn $"Automaton Size: %i{possiblyNegatedAut.Aut.Skeleton.States.Count}"


            sw.Start()
            let negativeAut = 
                if not possiblyNegatedAut.IsNegated then 
                    Util.LOGGER $"Start automaton negation..."
                    // Negate
                    match FsOmegaLib.Operations.AutomataOperations.complementToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                    | Success x -> x
                    | Fail err -> raise <| AnalysisException err
                else 
                    if mcOptions.IntermediateSimplification then 
                        Util.LOGGER $"Start automaton simplification..."
                        // Pass into spot (without any changes to the language) to enable easy simplication
                        match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) possiblyNegatedAut.Aut with
                        | Success x -> x
                        | Fail err -> raise <| AnalysisException err
                    else 
                        Util.LOGGER $"No automaton simplification..."
                        possiblyNegatedAut.Aut

            Util.LOGGERn $"Done. | Automaton Size: %i{negativeAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            Util.LOGGER $"Start projection..."
            sw.Restart()
            let nextAut = projectAwayAP negativeAut p
            Util.LOGGERn $"Done. | Automaton Size: %i{nextAut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

            Util.LOGGERn "=================================================="
            Util.LOGGERn ""

            generateAutomatonRec config mcOptions tsMap nonProjectedTraces remainingPrefix {PossiblyNegatedAutomaton.Aut = nextAut; IsNegated = true}


let generateAutomaton (config : SolverConfiguration) mcOptions (tsmap : Map<TraceVariable, GNBA<int, 'L>>) (nonProjectedTraces: Set<TraceVariable>) (quantifierPrefix : list<HyperQPTLQuantifier>) (formula : LTL<HyperQPTLAtom<'L>>) = 
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

    Util.LOGGERn "========================= LTL-to-GNBA ========================="
    Util.LOGGER $"Start LTL-to-GNBA translation..."
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    let aut =
        match FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA Util.DEBUG config.GetMainPath config.GetLtl2tgbaPath body with 
        | Success aut -> aut 
        | Fail err -> raise <| AnalysisException err 

    Util.LOGGERn $"Done. | Automaton Size: %i{aut.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

    Util.LOGGERn "=================================================="
    Util.LOGGERn ""

    generateAutomatonRec config mcOptions tsmap nonProjectedTraces quantifierPrefix {PossiblyNegatedAutomaton.Aut = aut; IsNegated = startWithNegated}
    
let modelCheck (config : SolverConfiguration) mcOptions (tsMap : Map<TraceVariable, GNBA<int, 'L>>) (hyperqptl : HyperQPTL<'L>) =
    let tsMapSimplified = 
        tsMap
        |> Map.map (fun pi gnba -> 
            if mcOptions.InitialSystemSimplification then 
                // We pass the gnba to spot to enable easy preprocessing 

                Util.LOGGERn $"========================= System Simplification for \"%s{pi}\" ========================="
                Util.LOGGERn $"Old Size: %i{gnba.Skeleton.States.Count}"
                Util.LOGGER $"Start GNBA simplification..."
                
                let sw = System.Diagnostics.Stopwatch()
                sw.Start()

                let gnba' = 
                    match FsOmegaLib.Operations.AutomatonConversions.convertToGNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath (Effort.HIGH) gnba with
                    | Success x -> x
                    | Fail err -> raise <| AnalysisException err

                Util.LOGGERn $"Done. | New Size: %i{gnba'.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

                Util.LOGGERn "=================================================="
                Util.LOGGERn ""

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

        Util.LOGGERn "========================= Emptiness Check ========================="
        Util.LOGGER $"Automaton size: %i{aut.Skeleton.States.Count}"
        Util.LOGGER $"Start emptiness check..."
        let sw = System.Diagnostics.Stopwatch()
        sw.Start()

        let res = 
            match FsOmegaLib.Operations.AutomataChecks.isEmpty Util.DEBUG config.GetMainPath config.GetAutfiltPath aut with
            | Success isEmpty ->
                if isNegated then
                    isEmpty
                else
                    not isEmpty
            | Fail err -> raise <| AnalysisException err

        Util.LOGGERn $"Done. | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"
        Util.LOGGERn "=================================================="
        Util.LOGGERn ""


        res, None

    else 
        Util.LOGGERn "========================= Emptiness Check / Witness Search ========================="
        Util.LOGGER $"Automaton size: %i{aut.Skeleton.States.Count}"
        Util.LOGGER $"Start GNBA-to-NBA translation..."
        let sw = System.Diagnostics.Stopwatch()
        sw.Start()

        let nba = 
            match FsOmegaLib.Operations.AutomatonConversions.convertToNBA Util.DEBUG config.GetMainPath config.GetAutfiltPath Effort.HIGH aut with
            | Success nba -> nba
            | Fail err -> raise <| AnalysisException err

        Util.LOGGERn $"Done. | New Size: %i{nba.Skeleton.States.Count} | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"

        Util.LOGGER $"Start lasso search in NBA..."
        sw.Restart()
        let res = AutomataUtil.shortestAcceptingPaths nba

        Util.LOGGERn $"Done. | Time: %i{sw.ElapsedMilliseconds}ms (%.4f{double(sw.ElapsedMilliseconds) / 1000.0}s) |"
        Util.LOGGERn "=================================================="
        Util.LOGGERn ""

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
                        | PropAtom _ -> raise <| AnalysisException $"Encountered a quantified propositional AP in the lasso, should not happen!"
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