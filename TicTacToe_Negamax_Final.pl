/*********************************
	DESCRIPTION DU JEU DU TIC-TAC-TOE
	*********************************/

	/*
	Une situation est decrite par une matrice 3x3.
	Chaque case est soit un emplacement libre (Variable LIBRE), soit contient le symbole d'un des 2 joueurs (o ou x)

	Contrairement a la convention du tp precedent, pour modeliser une case libre
	dans une matrice on n'utilise pas une constante speciale (ex : nil, 'vide', 'libre','inoccupee' ...);
	On utilise plutôt un identificateur de variable, qui n'est pas unifiee (ex : X, A, ... ou _) .
	La situation initiale est une "matrice" 3x3 (liste de 3 listes de 3 termes chacune)
	où chaque terme est une variable libre.	
	Chaque coup d'un des 2 joureurs consiste a donner une valeur (symbole x ou o) a une case libre de la grille
	et non a deplacer des symboles deja presents sur la grille.		
	
	Pour placer un symbole dans une grille S1, il suffit d'unifier une des variables encore libres de la matrice S1,
	soit en ecrivant directement Case=o ou Case=x, ou bien en accedant a cette case avec les predicats member, nth1, ...
	La grille S1 a change d'etat, mais on n'a pas besoin de 2 arguments representant la grille avant et apres le coup,
	un seul suffit.
	Ainsi si on joue un coup en S, S perd une variable libre, mais peut continuer a s'appeler S (on n'a pas besoin de la designer
	par un nouvel identificateur).
	*/

situation_initiale([ [_,_,_],
                     [_,_,_],
                     [_,_,_] ]).

situation_nulle([ [o,x,x],
                     [x,o,o],
                     [o,x,x] ]).

situation_perdante_x([ [o,x,o],
                     [x,o,o],
                     [o,x,x] ]).

situation_perdante_o([ [o,x,x],
                     [x,x,o],
                     [o,x,x] ]).



	% Convention (arbitraire) : c'est x qui commence

joueur_initial(x).


	% Definition de la relation adversaire/2

adversaire(x,o).
adversaire(o,x).


	/****************************************************
	 DEFINIR ICI a l'aide du predicat ground/1 comment
	 reconnaitre une situation terminale dans laquelle il
	 n'y a aucun emplacement libre : aucun joueur ne peut
	 continuer a jouer (quel qu'il soit).
	 ****************************************************/

situation_terminale(_Joueur, Situation) :-
    ground(Situation).

situation_terminale(J, Situation) :-
    heuristique(J,Situation,H),
    10000 is abs(H). 

	/***************************
	DEFINITIONS D'UN ALIGNEMENT
	***************************/

alignement(L, Matrix) :- ligne(    L,Matrix).
alignement(C, Matrix) :- colonne(  C,Matrix).
alignement(D, Matrix) :- diagonale(D,Matrix).

	/********************************************
	 DEFINIR ICI chaque type d'alignement maximal 
 	 existant dans une matrice carree NxN.
	 ********************************************/
	
ligne(L, M) :- nth1(_,M,L).

colonne(_,[],[]).
colonne(N,[C1|RestC],[M1|RestM]) :- nth1(N,M1,C1), colonne(N,RestC,RestM).
 
colonne(C,M) :- colonne(_,C,M).

	/* Definition de la relation liant une diagonale D a la matrice M dans laquelle elle se trouve.
		il y en a 2 sortes de diagonales dans une matrice carree(https://fr.wikipedia.org/wiki/Diagonale) :
		- la premiere diagonale (principale)  : (A I)
		- la seconde diagonale                : (Z R)
		A . . . . . . . Z
		. \ . . . . . / .
		. . \ . . . / . .
		. . . \ . / . . .
		. . . . X . . .
		. . . / . \ . . . 
		. . / . . . \ . .
		. / . . . . . \ .
		R . . . . . . . I
	*/
		
diagonale(D, M) :- 
	premiere_diag(1,D,M).

diagonale(D, M) :-
	seconde_diag(3,D,M).
	
premiere_diag(_,[],[]).
premiere_diag(K,[E|D],[Ligne|M]) :-
	nth1(K,Ligne,E),
	K1 is K+1,
	premiere_diag(K1,D,M).

seconde_diag(_,[],[]).
seconde_diag(K,[E|D],[Ligne|M]) :-
    nth1(K,Ligne,E),
	K1 is K-1,
	seconde_diag(K1,D,M).

%Test
test_diagonale(D):-
    situation_nulle(S), 
    diagonale(D,S).

test_colonne(C):-
    situation_nulle(S), 
    colonne(C,S).

test_ligne(L):-
    situation_nulle(S), 
    ligne(L,S).


	/*****************************
	 DEFINITION D'UN ALIGNEMENT 
	 POSSIBLE POUR UN JOUEUR DONNE
	 *****************************/

possible([X|L], J) :- unifiable(X,J), possible(L,J).
possible(  [],  _).

	/* Attention 
	il faut juste verifier le caractere unifiable
	de chaque emplacement de la liste, mais il ne
	faut pas realiser l'unification.
	*/

% A FAIRE 
unifiable(X,_) :- var(X).
unifiable(X,J) :- ground(X),X=J.
	
	/**********************************
	 DEFINITION D'UN ALIGNEMENT GAGNANT
	 OU PERDANT POUR UN JOUEUR DONNE J
	 **********************************/
	/*
	Un alignement gagnant pour J est un alignement
possible pour J qui n'a aucun element encore libre.
	*/
	
	/*
	Remarque : le predicat ground(X) permet de verifier qu'un terme
	prolog quelconque ne contient aucune partie variable (libre).
	exemples :
		?- ground(Var).
		no
		?- ground([1,2]).
		yes
		?- ground(toto(nil)).
		yes
		?- ground( [1, toto(nil), foo(a,B,c)] ).
		no
	*/
		
	/* Un alignement perdant pour J est un alignement gagnant pour son adversaire. */

% A FAIRE
alignement_gagnant([], _).
alignement_gagnant([Ali|Rest], J) :- ground(Ali),Ali=J,alignement_gagnant(Rest, J).

alignement_perdant(Ali, J) :- adversaire(J,I),alignement_gagnant(Ali,I).

% Tests
test_AG:-
    A=[x,x,x], alignement_gagnant(A, x).


test_AP:-
    A=[x,x,x], alignement_perdant(A, o).

	/* ****************************
	DEFINITION D'UN ETAT SUCCESSEUR
	****************************** */

	/* 
	Il faut definir quelle operation subit la matrice
	M representant l'Etat courant
	lorsqu'un joueur J joue en coordonnees [L,C]
	*/	

% A FAIRE
successeur(J, Etat,[L,C]) :- nth1(L,Etat,L1), nth1(C,L1,Elem),var(Elem), Elem=J.

%Test (on joue en [1,2] sur l'état initial vide)
test_successeur(Ini):-
    situation_initiale(Ini),
    successeur(x,Ini,[1,2]).

	/**************************************
   	 EVALUATION HEURISTIQUE D'UNE SITUATION
  	 **************************************/

	/*
	1/ l'heuristique est +infini si la situation J est gagnante pour J
	2/ l'heuristique est -infini si la situation J est perdante pour J
	3/ sinon, on fait la difference entre :
	   le nombre d'alignements possibles pour J
	moinsstique évalue quelle sont les chances de gagner pour un jo
 	   le nombre d'alignements possibles pour l'adversaire de J
*/


heuristique(J,Situation,H) :-		% cas 1
   H = 10000,				% grand nombre approximant +infini
   alignement(Alig,Situation),
   alignement_gagnant(Alig,J), !.
	
heuristique(J,Situation,H) :-		% cas 2
   H = -10000,				% grand nombre approximant -infini
   alignement(Alig,Situation),
   alignement_perdant(Alig,J), !.	


% on ne vient ici que si les cut precedents n'ont pas fonctionne,
% c-a-d si Situation n'est ni perdante ni gagnante.

% A FAIRE 					cas 3
heuristique(J,Situation,H) :- 
    adversaire(I,J),
    findall(1,(alignement(Ali,Situation),possible(Ali,J)),Liste1), length(Liste1,H1),
    findall(1,(alignement(Ali,Situation),possible(Ali,I)),Liste2), length(Liste2,H2),
    H is H1-H2.

%Test
test_heuristique1(H):- %Situation perdante pour x
  situation_perdante_x(S),heuristique(x, S,H).

test_heuristique2(H):- % Situation gagnante pour x
  situation_perdante_o(S),heuristique(x, S,H).

test_heuristique3(H):- % Situation nulle
  situation_nulle(S),heuristique(x, S,H).
































	/****************************************************
  	ALGORITHME MINMAX avec convention NEGAMAX : negamax/5
  	*****************************************************/

	/*
	negamax(+J, +Etat, +P, +Pmax, [?Coup, ?Val])

	SPECIFICATIONS :

	retourne pour un joueur J donne, devant jouer dans
	une situation donnee Etat, de profondeur donnee P,
	le meilleur couple [Coup, Valeur] apres une analyse
	pouvant aller jusqu'a la profondeur Pmax.

	Il y a 3 cas a decrire (donc 3 clauses pour negamax/5)
	
	1/ la profondeur maximale est atteinte : on ne peut pas
	developper cet Etat ; 
	il n'y a donc pas de coup possible a jouer (Coup = rien)
	et l'evaluation de Etat est faite par l'heuristique.

	2/ la profondeur maximale n'est pas  atteinte mais J ne
	peut pas jouer ; au TicTacToe un joueur ne peut pas jouer
	quand le tableau est complet (totalement instancie) ;
	il n'y a pas de coup a jouer (Coup = rien)
	et l'evaluation de Etat est faite par l'heuristique.

	3/ la profondeur maxi n'est pas atteinte et J peut encore
	jouer. Il faut evaluer le sous-arbre complet issu de Etat ; 

	- on determine d'abord la liste de tous les couples
	[Coup_possible, Situation_suivante] via le predicat
	 successeurs/3 (deja fourni, voir plus bas).

	- cette liste est passee a un predicat intermediaire :
	loop_negamax/5, charge d'appliquer negamax sur chaque
	Situation_suivante ; loop_negamax/5 retourne une liste de
	couples [Coup_possible, Valeur]

	- parmi cette liste, on garde le meilleur couple, c-a-d celui
	qui a la plus petite valeur (cf. predicat meilleur/2);
	soit [C1,V1] ce couple optimal. Le predicat meilleur/2
	effectue cette selection.

	- finalement le couple retourne par negamax est [Coup, V2]
	avec : V2 is -V1 (cf. convention negamax vue en cours).

A FAIRE : ECRIRE ici les clauses de negamax/5
.....................................
	*/
%negamax(+J, +Etat, +P, +Pmax, [?Coup, ?Val]).
negamax(J,E,P,P,[rien,V]):-
    heuristique(J,E,V), !.
negamax(J,E,_,_,[rien,V]):-
    situation_terminale(J,E),
    heuristique(J,E,V), ! .
negamax(J, Etat, P, Pmax, [Coup, Val]):-
    successeurs(J,Etat,Succ),
    loop_negamax(J,P,Pmax,Succ,SuccV),
    meilleur(SuccV,[C1,V1]),
    Coup=C1,
    Val is -V1.
     

	/*******************************************
	 DEVELOPPEMENT D'UNE SITUATION NON TERMINALE
	 successeurs/3 
	 *******************************************/

	 /*
   	 successeurs(+J,+Etat, ?Succ)

   	 retourne la liste des couples [Coup, Etat_Suivant]
 	 pour un joueur donne dans une situation donnee 
	 */

successeurs(J,Etat,Succ) :-
	copy_term(Etat, Etat_Suiv),
	findall([Coup,Etat_Suiv],
		    successeur(J,Etat_Suiv,Coup),
		    Succ).

%Test
test_successeurs(J,_,Succ):-
	situation_initiale(Ini), 
    successeurs(J, Ini, Succ).

	/*************************************
         Boucle permettant d'appliquer negamax 
         a chaque situation suivante :
	*************************************/

	/*
	loop_negamax(+J,+P,+Pmax,+Successeurs,?Liste_Couples)
	retourne la liste des couples [Coup, Valeur_Situation_Suivante]
	a partir de la liste des couples [Coup, Situation_Suivante]
	*/

loop_negamax(_,_, _  ,[],                []).
loop_negamax(J,P,Pmax,[[Coup,Suiv]|Succ],[[Coup,Vsuiv]|Reste_Couples]) :-
	loop_negamax(J,P,Pmax,Succ,Reste_Couples),
	adversaire(J,A),
	Pnew is P+1,
	negamax(A,Suiv,Pnew,Pmax, [_,Vsuiv]).

	/*

A FAIRE : commenter chaque litteral de la 2eme clause de loop_negamax/5,
	en particulier la forme du terme [_,Vsuiv] dans le dernier
	litteral ?
    
    
	*/

	/*********************************
	 Selection du couple qui a la plus
	 petite valeur V 
	 *********************************/

	/*
	meilleur(+Liste_de_Couples, ?Meilleur_Couple)

	SPECIFICATIONS :
	On suppose que chaque element de la liste est du type [C,V]
	- le meilleur dans une liste a un seul element est cet element
	- le meilleur dans une liste [X|L] avec L \= [], est obtenu en comparant
	  X et Y,le meilleur couple de L 
	  Entre X et Y on garde celui qui a la petite valeur de V.

A FAIRE : ECRIRE ici les clauses de meilleur/2
	*/
meilleur([Couple], Couple).
meilleur([[_,V1]|Rest], [C2,V2]):-
	    meilleur(Rest,[C2,V2]),
    	V1>V2.
meilleur([[C1,V1]|Rest], [C1,V1]):-
	    meilleur(Rest,[_,V2]),
    	V1=<V2.

%Test
testMeilleur(C1,C2,C3,C4):-
    meilleur([[_,1],[_,7],[_,26]],C1), 
    meilleur([[_,13],[test0,4],[_,3],[_,2]],C2), 
    meilleur([[test1,1],[_,3],[test2,1]],C3),     
    meilleur([[_,4235],[_,513],[_,24]],C4). 

	/******************
  	PROGRAMME PRINCIPAL
  	*******************/

main(B,V, Pmax) :-
	situation_initiale(Ini),
    joueur_initial(J),
    negamax(J,Ini,0,Pmax,[B,V]).

	/*
A FAIRE :
	Compléter puis tester le programme principal pour plusieurs valeurs de la profondeur maximale.
	Pmax = 1, 2, 3, 4 ...
	Commentez les résultats obtenus.
	*/
