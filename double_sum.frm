#-
#: Path summer
#include summer.h
#include IBIS.h
Off stats;
CFunction Log, PolyLog;

Local F = sum1(j1,1,j2-1)*sign(j1)*invbino(j2,j1)*den(j1)^2*S(R(1),j1)*S(R(1),j2-j1);
* We us IBIS for the inner inverse binomial sum:
Multiply replace_(j1,j,sum1,sum);
#call IBIS
* All the X vectors in the S-sums are trivial, i.e. have argument 1, 
* so we remove those:
id S(R(?n1),X(?n2),j?) = S(R(?n1),j);
Print +s;
.sort

* For the remaining sum, we can now go to summer:
Multiply -sum2(j2,1,inf)*den(j2)*den(j2+1);
Multiply replace_(j2,j1,sum2,sum1);
#call summer(1)
Print +s;
.sort

* We can now fill in the multiple zeta values:
#call tables(5)
id S(R(?n),inf) = SS(?n);
Transform SS explode(1,last);
#do k=1,5
	id SS(n1?,...,n`k'?) = Stab`k'(n1,...,n`k');
#enddo
SplitArg (inf), theta;
id theta(x?,inf) = 1;
id theta(inf) = 1;
Print +s;
.end
