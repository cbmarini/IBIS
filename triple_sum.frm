#-
#: Path ./xsummer
#include summer/summer.h
#include IBIS/IBIS.h
#include xsummer/declsums.h
#include xsummer/declvars.h

#define MAXWEIGHT "6"
#define EXPANDEP "1"
#define MAXSUM "2"
#define TRUNCEP "3"

Off statistics;

#procedure denapart(j)
	SplitArg (`j'),den;
	id den(`j') = den(0,`j');
	repeat id den(x1?,`j')*den(x2?,-`j') = den(x1+x2)*(den(x1,`j')+den(x2,-`j'));
	repeat id den(x1?!{x2?},`j')*den(x2?!{x1?},`j') = den(x2-x1)*(den(x1,`j')-den(x2,`j'));
	id den(x1?,x2?) = den(x1+x2);
	id den(x?number_) = 1/x;
#endprocedure

* We start with the inner IBIS sum
Local F = sum1(j1,1,j2)*sign(j1)*invbino(j2,j1)*den(j1)^2;
Multiply replace_(j1,j,sum1,sum);
* First, we rewrite the limits slightly such that the examples are in IBIS format:
#call Boundaryfix
Print +s;
.sort
#call IBIS
id S(R(n?),X(1),j?) = S(R(n),j);
Print +s;
.sort

* Next, we perform the second IBIS sum.
Local F = F*sum2(j2,1,j3-1)*invbino(j3,j2)*den(j2)*den(j2+1)*den(j3-j2)^2;
* We need to split the denominators first:
#call denapart(j2)
* We now go to the notation of IBIS
Multiply replace_(j2,j,sum2,sum);
#call Denflip(j3)
* We can now perform the next invbino sum
#call IBIS
id sign(j?) = pow(-1,j);
Print +s;
.sort

* For the final outer sum, we can use XSummer
Local F = F*sum3(j3,1,inf);
Multiply replace_(j3,j1,sum3,sum1);
* XSummer expects the indices of S to be positive. 
id S(R(?m),X(?x),j?) = S(R,RR(?m),X,XX(?x),j);
repeat;
	id S(R(?m),RR(m1?neg_,?m2),X(?x),XX(x1?,?x2),j?) = S(R(?m,-m1),RR(?m2),X(?x, -x1),XX(?x2),j);
	id S(R(?m),RR(m1?pos_,?m2),X(?x),XX(x1?,?x2),j?) = S(R(?m, m1),RR(?m2),X(?x, x1),XX(?x2),j);
endrepeat;
id S(R(?m),RR,X(?x),XX,j?) = S(R(?m),X(?x),j);
.sort

#call DoSum(1,1)
id den(x?number_) = 1/x;
id acc(x?) = x;
Print +s;
.end
