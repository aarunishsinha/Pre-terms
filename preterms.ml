type symbol = Sym of string										(*Name of the symbol is is of type symbol*)
type variable = string
type arity = Ari of int											(*Arity is of type arity*)
type pair = (symbol * arity)								(*A tuple containing the symbol and it's arity*)
type signature = (symbol * arity) list						(*List of such tuples*)
type term = V of variable | Node of symbol * (term list)	
type substitution = (variable * term) list 					(*defining an appropriate type for substitution*)
exception NOT_UNIFIABLE
(*Takes a signature and returns true if it has no negative arity*)
let rec no_neg s b = match s with
					| [] -> false
					| [(sy,a)] -> begin
									match a with
									| Ari(t) -> if t < 0 then false else true
					end
					| x::xs -> begin
						let (sy, a) = x in
						match a with
						| Ari(t) -> if t < 0 then false else (no_neg xs b)
					end
				;;
(*Takes a signature and returns true if it has at least one zero arity pair*)
let rec has_zero s b = match s with 
						| [] -> false
						| [(sy, a)] -> begin
							match a with 
							| Ari(t) -> if t==0 then true else false
						end
						| x::xs -> begin
							let (sy, a) = x in
							match a with 
							| Ari(t) -> if t == 0 then true else (has_zero xs b)
						end
					;;
(*Checks presence of a given symbol in a given pair list*)
let rec check_repeat p b s = match s with 
							| [] -> false
							| [(sy, a)] -> begin
								let (sy1, a1) = p in
								match sy, sy1 with
								| Sym(x), Sym(y) -> if (String.equal x y) then false else true
							end
							| x::xs -> begin
								let (sy, a) = x in
								let (sy1, a1) = p in
								match sy, sy1 with 
								| Sym(s1), Sym(s2) -> if (String.equal s1 s2) then false else (check_repeat p b xs)
							end
						;;
(*Checks repetitions of symbols in a given signature*)
let rec check_repeat_help s = match s with
							| [] -> false 
							| [(sy, a)] -> true
							| x::xs -> if (check_repeat x true xs) then (check_repeat_help xs) else false
						;;
(*Given a signature, if the signature is valid then it returns true else return false*)
let check_sig (s: signature) = if ((check_repeat_help s)&&(has_zero s false)&&(no_neg s true)) then true else false;;
(*Returns true if the size of the term list of a term is equal to the arity of the symbol in that term*)
let check_arity tl a1 = match a1 with 
						| Ari(x) -> if (x == List.length tl) then true else false
						;;
(*Checks if a term of type Node is valid or not*)
let rec check_symbol sy s tl = match s with
							| [] -> false
							| [(sy1, a1)] -> begin
								match sy, sy1 with
								| Sym(x), Sym(y) -> if (String.equal x y) then (true&&(check_arity tl a1)) else false					(*If symbol is present in the signature then checks if the number of children of the symbol is equal to it's arity*)
							end
							| x::xs -> begin
								let (sy1, a1) = x in
								match sy, sy1 with
								| Sym(s1), Sym(s2) -> if (String.equal s1 s2) then (true&&(check_arity tl a1)) else (check_symbol sy xs tl)
							end
						;;
(*Returns true if the given term is valid else false*)
let wfterm (t: term) (s: signature) = match t with 							(*s is a valid signature verfied by check_sig function*)
									| V(x) -> true							(*A term having a variable is vacuously true*)
									| Node(sy, tl) -> (check_symbol sy s tl)
								;;
(*Retruns the height of a given term*)
let rec ht (t: term) = match t with 
						| V(x) -> 1											(*Since variables are present only at the leaves so their height would be 1*)
						| Node(sy, tl) -> (1 + (List.fold_left (fun x y -> if x > y then x else y) 0 (List.map ht tl)))	(*For a Node map the term list with ht function and *)
						;;						
(*Returns the size of a given term excluding the symbol sy*)
let rec size_help (t: term) = match t with
						| V(x) -> 0															(*Not counting the variables as their count is included in List.length*)
						| Node(sy, tl) -> ((List.length tl) + (List.fold_left (fun x y -> x+y) 0 (List.map size_help tl))) 			(*For each Node the term list length is added to the current value of size*)
					;;
(*Returns the size of a given term*)
let size (t: term) = ((size_help t) + 1);;  									(* + 1 is done to include the count of the symbol (or root of the tree)*)
(*Appends two lists*)
let insert l1 l2 = match l1 with 
  					| [] -> l2
 					| _ -> (List.append l1 l2);;
(*Goes through all the terms in the term list of the term an adds all the variables in a list and returns the list*)
let rec vars_help (t: term) = match t with 
						| V(x) -> [(V(x))]										(*Returning a variable list instead of variable to aid in appending*)
						| Node(sy, tl) -> (List.fold_right (insert) (List.map vars_help tl) [])
					;; 
let uniq_cons x xs = if List.mem x xs then xs else x :: xs;;	(*Removes the duplicates of a particular element in a given list and then returns the list*)
let remove_duplicates xs = List.fold_right uniq_cons xs [];;	(*Goes through all the elements of the list checking their duplicates and removing them*)
(*Returns a list containing all the variables in a term without any repetitions*)
let vars (t: term) = remove_duplicates (vars_help t);;
(*Given a variable and a substitution returns the term corresponding to the the variable v by searching v in the list of (variables, terms)*)
let rec sub_var (sub: substitution) (v: variable) = match sub with
												| [] -> (V(v))
												| x::xs -> begin
													match x with
													| (var, ter) -> begin
														match var, v with
														| v1, v2 -> if (String.equal v1 v2) then ter else (sub_var xs v)
													end
												end
											;;
(*Given a term t and a substitution sub, applies the Unique Homomorphic Extension of sub to t*)
let rec subst (sub: substitution) (t: term) = match t with
											| V(x) -> sub_var sub x
											| Node(sy, tl) -> Node(sy, List.map (subst sub) tl)
										;;
(*Given a substitution and a pair of variable and term, returns the pair containing the variable and the Unique Homomorphic Extension of s to t*)
let rec comp_help (s: substitution) p = match p with 
										| (v, t) -> (v, (subst s t))
									;;
(*Returns a list containing the Unique Homomorphic Extension of s to t of all the terms in a substitution*)
let comp_help2 (s1: substitution) (s2: substitution) = (List.map (comp_help s2) s1);;
(*Predicate that checks that the variables of two pairs of variables and terms are same or not*)
let check p1 p2 = match p1, p2 with
				| (v1, t1), (v2, t2) -> if (String.equal v2 v1) then true else false
			;;
(*Checks if a pair of variable and term is present in the substitution*)
let check_present s p = List.exists (check p) s;;
(*Adds all the elements of s2 that are not in s1 and returns the composition of s1 and s2*)
let rec comp (s1: substitution) (s2: substitution) = match s2 with 
															| [] -> s1
															| x::xs ->  begin
																if (check_present s1 x) then (comp s1 xs) else (comp (x::s1) xs) 
															end
														;;
(*Checks if a veriable is present in the given term list or not*)
let rec var_present_term tl v = match tl with
						| [] -> false
						| x::xs -> begin
							match x with 
							| V(va) -> if (String.equal va v) then true else var_present_term xs v
							| Node(sym, tel) -> (var_present_term tel v) || (var_present_term xs v) 			(*If the term is a node the go check in the term list of that Node and also in the term list of which Node was a part of*)
						end
					;;
(*Returns the Most General Unifier of two terms if it exists else raises an exception*)
let rec mgu_help terl1 terl2 (t1: term) (t2: term) = match t1, t2 with 
									| V(x), V(y) -> begin 											(*When both the terms are variables*)
										if (var_present_term terl2 x) then raise NOT_UNIFIABLE else (*If variable in t2 is already present in the term list of which t2 is a part of then the terms are not unifiable*)
											if (String.equal x y) then [] else [(x, (V(y)))] 		(*If the variables are same then do nothing else create an appropriate substitution*)
									end
									| V(x), Node(sy, tl) -> if (var_present_term tl x)||(var_present_term terl2 x) then raise NOT_UNIFIABLE else [(x, Node(sy, tl))] 	(*If the variable in t1 is already present in the Node of t2 then the terms aren't unnifiable*)
									| Node(sy, tl), V(x) -> if (var_present_term tl x)||(var_present_term terl1 x) then raise NOT_UNIFIABLE else [(x, Node(sy, tl))]
									| Node(sy1, tl1), Node(sy2, tl2) -> begin 						(*When both the terms are Nodes*)
										match sy1, sy2 with
										| Sym(a), Sym(b) -> begin
											if not(String.equal a b) then raise NOT_UNIFIABLE else 		(*Check if Symbols of the two are equal or not, if not raise exception*)
												if not((List.length tl1)==(List.length tl2)) then raise NOT_UNIFIABLE else 		(*then check if the length of their term lists are same or not, if not raise exception*)
													begin
														match tl1, tl2 with
														| [], [] -> []
														| [], _::_ -> []
														| _::_, [] -> []
														| x::xs, y::ys -> (mgu_help tl1 tl2 x y) @ (List.concat (List.map2 (mgu_help tl1 tl2) xs ys))
													end
										end
									end
								;;
(*Returns the Most General Unifier of t1 and t2, wrapper for mgu_help*)
let mgu (t1: term) (t2: term) = mgu_help [] [] t1 t2;;