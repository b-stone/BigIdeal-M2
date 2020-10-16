--------------------------------------------------------------------------
-- PURPOSE : Compute the ideals in "Ideals with Larger Projective 
-- Dimension and Regularity" by J. Beder, J. McCullough, L. Nunez-Betancourt, 
-- A. Seceleanu, B. Snapp and B. Stone
--
-- Copyright (C) 2011 Jesse Beder, Jason McCullough, Luis Nunez-Betancourt, 
-- Alexandra Seceleanu, Bart Snapp and Branden Stone
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the GNU General Public License version 2
-- as published by the Free Software Foundation.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--------------------------------------------------------------------------
--
--
newPackage(
	"BigIdeal",
    	Version => "1.1", 
    	Date => "January 13, 2011",
    	Authors => {{Name => "Jesse Beder"},
	     {Name => "Jason McCullough"},
	     {Name => "Luis Nunez-Betancourt"},
	     {Name => "Alexandra Seceleanu"},
	     {Name => "Bart Snapp"},
	     {Name => "Branden Stone"}},
    	Headline => "Ideals with Large Projective Dimension and Regularity",
    	DebuggingMode => true
    	)

export{"bigIdeal", "jasonIdeal", "socleCheck", "BaseField"}

-- Usage: Type "load bigIdeal.m2" to load the commands in this file.
-- Then the command "bigIdeal(g,{m_1,...,m_n})" generates the ideal $I_{g,(m_1,...,m_n)}$ in the paper.
--
-- input: g = number of generators
--     	  M = list
-- output: Ideal with high prjective dimension
--
-- Note: if #M = 1 then us function K below
--       g >= 2, #M >= 2
bigIdeal = method( Options => { BaseField => QQ } )
bigIdeal(ZZ,List) := opt -> (g,M) -> ( 
     n := #M;
     if n == 1 
     then ( return jasonIdeal(g,1,M_0+1, BaseField=>opt.BaseField);	  
	   )
     else (
     	  d := i -> sum(take(M, -(n - i)-1))+1;	  
	  t := symbol t;
     	  C := ZZ[t_1..t_g];
     	  m := last M;  
     	  ind := (g,M) ->  apply(apply( toList fold((i,j) -> i**j,
	  	append(
     		     apply(drop(M,-1), m -> 
	  		  set flatten apply(select(terms product(1..g, j -> 
			 		 sum(m, i -> t_j^i)), i -> 
		    		    first degree i == m),exponents)),
     		     set flatten apply(select(terms product(1..g, j -> sum(m+1, i -> t_j^i)), 
	       		       i -> first degree i == m),exponents)))/deepSplice,toList),i -> transpose matrix i);     
          front := (g,M) ->if #M == 1 then apply(flatten apply(M, m -> flatten apply(select(terms product(1..g, j -> 
			 	   sum(m, i -> t_j^i)), i -> 
		    	      first degree i == m), exponents)),i->transpose matrix {i}) else apply(apply( toList fold((i,j) -> i**j,
     	       		 apply(M, m -> set flatten apply(select(terms product(1..g, j -> 
			 		     sum(m, i -> t_j^i)), i -> 
		    			first degree i == m),
	       			   exponents)))
     		    /deepSplice,toList),i -> transpose matrix i);
     	  middle := (i,g,M) -> (
	       A := mutableMatrix(ZZ,g,2);
	       A_(0,0) = M_(i); 	    
	       A_(0,1) = d(i+2);
	       {matrix A}|toList(apply (0..g-2, i-> matrix rowSwap(A,i,i+1)))
	       );
     	  matrixListPre := flatten toList apply(1..n-2, 
	       i -> flatten apply(front(g,take(M,i)),j -> flatten apply(middle(i,g,M), k -> j|k)));
     	  matrixList := apply(middle(0,g,M)|matrixListPre, i -> i | map(ZZ^g, ZZ^(n-rank source i), 0));
          k := opt.BaseField;
	  indList := ind(g,M);
	  xvarlist := flatten for j from 1 to n list for i from 1 to g list (i,j); 
	  x := symbol x;
	  y := symbol y;
     	  B := k[apply(xvarlist, i -> x_i), apply(indList, i -> y_i),MonomialOrder =>GRevLex];
     	  I := ideal(apply(x_(1,1)..x_(g,1), i -> i^(d 1)),sum apply(matrixList,m-> product flatten for i to g-1 list ( for j to n-1 list x_(i+1,j+1)^(m_(i,j))))+sum apply(indList,m-> (product flatten for i to g-1 list ( for j to n-1 list x_(i+1,j+1)^(m_(i,j))))*y_m));
	  );
     I
)     

-- Gives ideals defined by J. McCullough and is the special case of function bigIdeal above. 
-- See http://arxiv.org/abs/1005.3361 or Proc. of the AMS article "A Family of Ideals with Few Generators in Low Degree and Large Projective Dimension"
--  
-- input: m = number of generators minus n ( m = g )
--     	  n = number of times to include y's
-- 	  d = degree of the generators
-- output: ideal with large progective dimension.
--
jasonIdeal = method( Options => { BaseField => QQ } )
jasonIdeal(ZZ,ZZ,ZZ) := opt -> (m,n,d) -> (
    x := symbol x;
    F := opt.BaseField;
    A := F[x_1..x_m];
    L := flatten entries basis(d-1,A);
    l := length L;
    y := symbol y;
    B := F[x_1..x_m,y_(1,1)..y_(l,n)]; -- not a local variable
    I := ideal apply(x_1..x_m, i -> i^d) + ideal apply(1..n, k -> sum(1..l, j -> sub(L_(j-1),B)*y_(j,k)));
    I
    )

-- input: I = an ideal
--        s = a ring element
-- output: a boolean value representing whether or not s is a nonzero socle element of R/I.  
--         If so, then it follows that R/I has maximal projective dimension.
socleCheck = method()
socleCheck(Ideal,RingElement) := (I,s) -> (
     if (s%I) == 0 then r := false;
     if (s%I) == 0 then return false;
     all(gens ring I, i -> ((i*s)%I) == 0)
     );

------------------------------------------------------------------
 
 
beginDocumentation()
needsPackage "SimpleDoc"
debug SimpleDoc

doc ///
  Key
    BigIdeal
  Headline
    Ideals with Large Projective Dimension and Regularity.
  Description
    Text
       The goal of this package is to provide commands to generate the ideals
       in "Ideals with Larger Projective Dimension and Regularity" by Beder,
       McCullough, Nunez, Seceleanu, Snapp and Stone.
///

doc ///
  Key
    bigIdeal
    (bigIdeal,ZZ,List)
    BaseField
  Headline
    Constructs one of the family of ideals with large projective dimension and regularity.
  Usage
    bigIdeal(g,L)
    bigIdeal(g,{2,1,3})
  Inputs
    g:ZZ
      Assumed to be at least 2.
    L:List
      List of integers {m_1,...m_n} such that m_n is nonnegative, m_{n-1} > 0 and all other
      m_i > 1.
  Outputs
    I:Ideal
      An ideal with g+1 generators in degree m_1+...+m_n+1.
  Description
   Text
     The ideal returned has g generators of the form x_i^d and 1 generator using the remaining
     variables.  Note that the y variables are indexed by matrices with entries prescribed by
     the entries of L.  The special case where L contains a single integer reverts to the ideals
     defined by the jasonIdeal command.
   Example
     bigIdeal(2,{3,1})
     bigIdeal(2,{2,1,2})
     bigIdeal(3,{2})
///

doc ///
  Key
    jasonIdeal
    (jasonIdeal,ZZ,ZZ,ZZ)
  Headline
    Constructs one of the family of ideals in "A Family of Ideals with Few Generators in Low Degree and Large Projective Dimension" by Jason McCullough.
  Usage
    x = jasonIdeal(m,n,d)
  Inputs
    m:ZZ
      Assumed to be at least 2.
    n:ZZ
      Assumed to be at least 1.
    d:ZZ
      Assumed to be at least 1.
  Outputs
    I:Ideal
      An ideal with m+n generators in degree d and with pd(R/I) = (m + d - 2)!/((m-1)!(d-1)!).
  Description
   Text
     The ideal returned has m generators of the form x_i^d and n generators each of which
     are a sum of the y_i variables times each of the degree-(d-1) monomials in the x_is.
   Example
     jasonIdeal(3,1,3)
///

doc ///
  Key
    socleCheck
    (socleCheck,Ideal,RingElement)
  Headline
    Checks where a ring element is nonzero is nonzero in socle(R/I) for an ideal I.
  Usage
    socleCheck(I,s)
  Inputs
    I:Ideal
    s:RingElement
  Outputs
    x:Boolean
      True if s is in (I:m) - I.  False otherwise.
  Description
   Text
     This function merely checks whether every variable multiplies s into I and that s is not already in I.
   Example
     R = QQ[x,y];
     I = ideal(x^2,y^2);
     socleCheck(I,x*y);
     socleCheck(I,x^2);
     socleCheck(I,x);
///
