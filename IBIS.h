*--#[ Declaration of variables
* Defining all the symbols and function that we use internally and externally
S a,b,c,d,e,w,x,y,z,n,k,m,jjj,jj,j;
CF g, g1, GG, TT, RU, RL, den, R, S, X, sum, invbino, bino, sign;
* Here we define the dollar variables that we will later use for checks
#$zeroindex = 0;
#$check1 = 0;
#$check2 = 0;
#$check3 = 0;
#$check4 = 0;
#$check5 = 0;
#$check6 = 0;
#$check7 = 0;
#$check8 = 0;
#$check9 = 0;
#$check11 = 0;
#$check12 = 0;
#$check98 = 0;
#$check99 = 0;
#$denflip = 0;
#$boundarycheck = 0;
*--#]

*--#[ Procedures

*--#[ Synchronization
#procedure Synchronization
*
* The procedure for synchronizing the fixed sign inverse binomial sums. The order of the subprocedures is put in such 
* a way that it first looks for a inverse binomial sum with two S-sums, then containing 1 S-sum and as a last step 0 S-sums.
*

*--#[ Synchronization of invbino sums containing 2 S-sums

*--#[ c>1 and c<0

#do i = 1,1

*--#[ Sign altering
* Case c>1 and q_1>=0 (sommetjes equation 7.42)
id TT(R,X,RU(b?,?a),RL(d?{>=0},?x),k?{>-1},n?,c?{>1}) = -(n+1)*den(c-1)^k*TT(R,X,RU(b,?a),RL(d,?x),1,n+1,0)
        + sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*TT(R,X,RU(b,?a),RL(d,?x),jjj,n+1,c-1))
        - sum_(jjj,1,d+1,binom_(d+k-jjj,k-1)*(n+1)*sign(d-jjj)*den(c-1)^(d+k-jjj+1)*TT(R,X,RU(b,?a),RL(?x),jjj,n+1,0))
        - sum_(jjj,1,k,binom_(d+k-jjj,d)*(n+1)*sign(d)*den(c-1)^(d+k-jjj+1)*TT(R,X,RU(b,?a),RL(?x),jjj,n+1,c-1));
* Case c>1 and q_1<0 (sommetjes equation 7.43) 
id TT(R,X,RU(b?,?a),RL(d?{<0},?x),k?{>-1},n?,c?{>1}) = -(n+1)*den(c-1)^k*TT(R,X,RU(b,?a),RL(d,?x),1,n+1,0)
        + sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*TT(R,X,RU(b,?a),RL(d,?x),jjj,n+1,c-1))
        - sum_(jjj,1,abs_(d)+1,binom_(abs_(d)+k-jjj,k-1)*(n+1)*sign(abs_(d)-jjj)*den(c-1)^(abs_(d)+k-jjj+1)*GG(R,X,RU(b,?a),RL(?x),jjj,n+1,0))
        - sum_(jjj,1,k,binom_(abs_(d)+k-jjj,abs_(d))*(n+1)*sign(abs_(d))*den(c-1)^(abs_(d)+k-jjj+1)*GG(R,X,RU(b,?a),RL(?x),jjj,n+1,c-1));
* Case c=-1, p_1>=0 and q_1>=0 (sommetjes equation 7.51)
id TT(R,X,RU(b?{>=0},?a),RL(d?{>=0},?x),k?{>-1},n?,-1) = TT(R,X,RU(b,?a),RL(d,?x),k,n,0)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(n)^(b+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n)^(b+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,0) + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(n)^(b+1+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*(TT(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*TT(R,X,RU(b,?a),RL(?x),jjj,n,-1));
* Case c=-1, p_1>=0 and q_1<0 (sommetjes equation 7.52)
id TT(R,X,RU(b?{>=0},?a),RL(d?{<0},?x),k?{>-1},n?,-1) = TT(R,X,RU(b,?a),RL(d,?x),k,n,0)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(n)^(b+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n)^(b+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,0) + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(n)^(b+1+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*(GG(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*GG(R,X,RU(b,?a),RL(?x),jjj,n,-1));
* Case c=-1, p_1<0 and q_1>=0 (sommetjes equation 7.53)
id TT(R,X,RU(b?{<0},?a),RL(d?{>=0},?x),k?{>-1},n?,-1) = TT(R,X,RU(b,?a),RL(d,?x),k,n,0)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,0) - S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*(TT(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*TT(R,X,RU(b,?a),RL(?x),jjj,n,-1));
* Case c=-1, p_1<0 and q_1<0 (sommetjes equation 7.54)
id TT(R,X,RU(b?{<0},?a),RL(d?{<0},?x),k?{>-1},n?,-1) = TT(R,X,RU(b,?a),RL(d,?x),k,n,0)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,0) - S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*(GG(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*GG(R,X,RU(b,?a),RL(?x),jjj,n,-1));
* Case c=-2, p_1>=0 and q_1>=0 (sommetjes equation 7.51)
id TT(R,X,RU(b?{>=0},?a),RL(d?{>=0},?x),k?{>-1},n?,-2) = TT(R,X,RU(b,?a),RL(d,?x),k,n,-1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(n-1)^(b+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n-1)^(b+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,-1) + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(b,?a),X(1),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(n-1)^(b+1+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n-1)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(2)^(d+k-jjj)*(TT(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(2)^(d+k-jjj)*TT(R,X,RU(b,?a),RL(?x),jjj,n,-2));
* Case c=-2, p_1>=0 and q_1<0 (sommetjes equation 7.52)
id TT(R,X,RU(b?{>=0},?a),RL(d?{<0},?x),k?{>-1},n?,-2) = TT(R,X,RU(b,?a),RL(d,?x),k,n,-1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(n-1)^(b+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n-1)^(b+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,-1) + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(b,?a),X(1),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(n-1)^(b+1+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n-1)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(2)^(abs_(d)+k-jjj)*(GG(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(2)^(abs_(d)+k-jjj)*GG(R,X,RU(b,?a),RL(?x),jjj,n,-2));
* Case c=-2, p_1<0 and q_1>=0 (sommetjes equation 7.53)
id TT(R,X,RU(b?{<0},?a),RL(d?{>=0},?x),k?{>-1},n?,-2) = TT(R,X,RU(b,?a),RL(d,?x),k,n,-1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,-1) - S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(b,?a),X(1),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(2)^(d+k-jjj)*(TT(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(2)^(d+k-jjj)*TT(R,X,RU(b,?a),RL(?x),jjj,n,-2));
* Case c=-2, p_1<0 and q_1<0 (sommetjes equation 7.54)
id TT(R,X,RU(b?{<0},?a),RL(d?{<0},?x),k?{>-1},n?,-2) = TT(R,X,RU(b,?a),RL(d,?x),k,n,-1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,-1) - S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(b,?a),X(1),n-1,nargs_(?a)) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?x),X(1),1,nargs_(?x))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(2)^(abs_(d)+k-jjj)*(GG(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(2)^(abs_(d)+k-jjj)*GG(R,X,RU(b,?a),RL(?x),jjj,n,-2));
* Case c<-2, p_1>=0 and q_1>=0 (sommetjes equation 7.51)
id TT(R,X,RU(b?{>=0},?a),RL(d?{>=0},?x),k?{>-1},n?,c?{<-2}) = TT(R,X,RU(b,?a),RL(d,?x),k,n,c+1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(1+c+n)^(b+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(1+c+n)^(b+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,c+1) + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(b,?a),X(1),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(-c)^(d+k-jjj)*(TT(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(-c)^(d+k-jjj)*TT(R,X,RU(b,?a),RL(?x),jjj,n,c));
* Case c<-2, p_1>=0 and q_1<0 (sommetjes equation 7.52)
id TT(R,X,RU(b?{>=0},?a),RL(d?{<0},?x),k?{>-1},n?,c?{<-2}) = TT(R,X,RU(b,?a),RL(d,?x),k,n,c+1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(1+c+n)^(b+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(1+c+n)^(b+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,c+1) + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(b,?a),X(1),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(TT(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?x),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(-c)^(abs_(d)+k-jjj)*(GG(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(-c)^(abs_(d)+k-jjj)*GG(R,X,RU(b,?a),RL(?x),jjj,n,c));
* Case c<-2, p_1<0 and q_1>=0 (sommetjes equation 7.53)
id TT(R,X,RU(b?{<0},?a),RL(d?{>=0},?x),k?{>-1},n?,c?{<-2}) = TT(R,X,RU(b,?a),RL(d,?x),k,n,c+1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,c+1) - S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(b,?a),X(1),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(-c)^(d+k-jjj)*(TT(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(-c)^(d+k-jjj)*TT(R,X,RU(b,?a),RL(?x),jjj,n,c));
* Case c<-2, p_1<0 and q_1<0 (sommetjes equation 7.54)
id TT(R,X,RU(b?{<0},?a),RL(d?{<0},?x),k?{>-1},n?,c?{<-2}) = TT(R,X,RU(b,?a),RL(d,?x),k,n,c+1)
      + sign(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,c+1) - S(R(d,?x),X(1),n-1,nargs_(?x))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU(d,?x),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(b,?a),X(1),jj,nargs_(?a))) + den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(TT(R,X,RU(b,?a),RL(d,?x),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(b,?a),X(1),1,nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(d,?x),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?x),X(1),n-jj,nargs_(?x))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?x),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?x),X(1),n-1,nargs_(?x))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(-c)^(abs_(d)+k-jjj)*(GG(R,X,RU(b,?a),RL(?x),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*den(jj)^(jjj)*S(R(?x),X(),jj,nargs_(?x))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(-c)^(abs_(d)+k-jjj)*GG(R,X,RU(b,?a),RL(?x),jjj,n,c));
*--#]
.sort
*--#[ Fixed sign
* Case c>1 and q_1>=0 (sommetjes equation 7.361)
id GG(R,X,RU(b?,?a),RL(d?{>=0},?x),k?{>-1},n?,c?{>1}) = (n+1)*den(c-1)^k*GG(R,X,RU(b,?a),RL(d,?x),1,n+1,0)
        - sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*GG(R,X,RU(b,?a),RL(d,?x),jjj,n+1,c-1))
        + sum_(jjj,1,d+1,binom_(d+k-jjj,k-1)*(n+1)*sign(d-jjj)*den(c-1)^(d+k-jjj+1)*GG(R,X,RU(b,?a),RL(?x),jjj,n+1,0))
        + sum_(jjj,1,k,binom_(d+k-jjj,d)*(n+1)*sign(d)*den(c-1)^(d+k-jjj+1)*GG(R,X,RU(b,?a),RL(?x),jjj,n+1,c-1));
* Case c>1 and q_1<0 (sommetjes equation 7.362)
id GG(R,X,RU(b?,?a),RL(d?{<0},?x),k?{>-1},n?,c?{>1}) = (n+1)*den(c-1)^k*GG(R,X,RU(b,?a),RL(d,?x),1,n+1,0)
        - sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*GG(R,X,RU(b,?a),RL(d,?x),jjj,n+1,c-1))
        + sum_(jjj,1,abs_(d)+1,binom_(abs_(d)+k-jjj,k-1)*(n+1)*sign(abs_(d)-jjj)*den(c-1)^(abs_(d)+k-jjj+1)*TT(R,X,RU(b,?a),RL(?x),jjj,n+1,0))
        + sum_(jjj,1,k,binom_(abs_(d)+k-jjj,abs_(d))*(n+1)*sign(abs_(d))*den(c-1)^(abs_(d)+k-jjj+1)*TT(R,X,RU(b,?a),RL(?x),jjj,n+1,c-1));
* Case c=-1, p_1>=0 and q_1>=0 (sommetjes equation 7.379)
id GG(R,X,RU(b?{>=0},?a),RL(d?{>=0},?e),k?{>-1},n?,-1) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,0)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(n)^(b+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n)^(b+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,0) - S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(n)^(b+1+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*(GG(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*GG(R,X,RU(b,?a),RL(?e),jjj,n,-1));
* Case c=-1, p_1>=0 and q_1<0 (sommetjes equation 7.380)
id GG(R,X,RU(b?{>=0},?a),RL(d?{<0},?e),k?{>-1},n?,-1) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,0)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(n)^(b+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n)^(b+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,0) - S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(n)^(b+1+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*(TT(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*TT(R,X,RU(b,?a),RL(?e),jjj,n,-1));
* Case c=-1, p_1<0 and q_1>=0 (sommetjes equation 7.381)
id GG(R,X,RU(b?{<0},?a),RL(d?{>=0},?e),k?{>-1},n?,-1) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,0)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(n)^(abs_(b)+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,0) + sign(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*(GG(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*GG(R,X,RU(b,?a),RL(?e),jjj,n,-1));
* Case c=-1, p_1<0 and q_1<0 (sommetjes equation 7.382)
id GG(R,X,RU(b?{<0},?a),RL(d?{<0},?e),k?{>-1},n?,-1) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,0)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-1)^k
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(n)^(abs_(b)+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,0) + sign(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*(TT(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*TT(R,X,RU(b,?a),RL(?e),jjj,n,-1));
* Case c=-2, p_1>=0 and q_1>=0 (sommetjes equation 7.379)
id GG(R,X,RU(b?{>=0},?a),RL(d?{>=0},?e),k?{>-1},n?,-2) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,-1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(n-1)^(b+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n-1)^(b+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,-1) - S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n-1)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*den(n-1)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(b,?a),X(1),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(n-1)^(b+1+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n-1)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(2)^(d+k-jjj)*(GG(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(2)^(d+k-jjj)*GG(R,X,RU(b,?a),RL(?e),jjj,n,-2));
* Case c=-2, p_1>=0 and q_1<0 (sommetjes equation 7.380)
id GG(R,X,RU(b?{>=0},?a),RL(d?{<0},?e),k?{>-1},n?,-2) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,-1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(n-1)^(b+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n-1)^(b+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,-1) - S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n-1)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*den(n-1)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(b,?a),X(1),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(n-1)^(b+1+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n-1)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(2)^(abs_(d)+k-jjj)*(TT(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(2)^(abs_(d)+k-jjj)*TT(R,X,RU(b,?a),RL(?e),jjj,n,-2));
* Case c=-2, p_1<0 and q_1>=0 (sommetjes equation 7.381)
id GG(R,X,RU(b?{<0},?a),RL(d?{>=0},?e),k?{>-1},n?,-2) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,-1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(n-1)^(abs_(b)+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,-1) + sign(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n-1)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*den(n-1)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(b,?a),X(1),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(2)^(d+k-jjj)*(GG(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(2)^(d+k-jjj)*GG(R,X,RU(b,?a),RL(?e),jjj,n,-2));
* Case c=-2, p_1<0 and q_1<0 (sommetjes equation 7.382)
id GG(R,X,RU(b?{<0},?a),RL(d?{<0},?e),k?{>-1},n?,-2) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,-1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n-2)^k
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(n-1)^(abs_(b)+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,-1) + sign(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(n-1)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - den(n)*den(n-1)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(b,?a),X(1),n-1,nargs_(?a)) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(d,?e),X(1),1,nargs_(?e))*S(R(?a),X(),n-1,nargs_(?a)) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(2)^(abs_(d)+k-jjj)*(TT(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(2)^(abs_(d)+k-jjj)*TT(R,X,RU(b,?a),RL(?e),jjj,n,-2));
* Case c<-2, p_1>=0 and q_1>=0 (sommetjes equation 7.379)
id GG(R,X,RU(b?{>=0},?a),RL(d?{>=0},?e),k?{>-1},n?,c?{<-2}) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,c+1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(1+c+n)^(b+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(1+c+n)^(b+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,c+1) - S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(b,?a),X(1),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(-c)^(d+k-jjj)*(GG(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(-c)^(d+k-jjj)*GG(R,X,RU(b,?a),RL(?e),jjj,n,c));
* Case c<-2, p_1>=0 and q_1<0 (sommetjes equation 7.380)
id GG(R,X,RU(b?{>=0},?a),RL(d?{<0},?e),k?{>-1},n?,c?{<-2}) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,c+1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(1+c+n)^(b+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(1+c+n)^(b+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,c+1) - S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(b,?a),X(1),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(GG(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL(d,?e),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(-c)^(abs_(d)+k-jjj)*(TT(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(-c)^(abs_(d)+k-jjj)*TT(R,X,RU(b,?a),RL(?e),jjj,n,c));
* Case c<-2, p_1<0 and q_1>=0 (sommetjes equation 7.381)
id GG(R,X,RU(b?{<0},?a),RL(d?{>=0},?e),k?{>-1},n?,c?{<-2}) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,c+1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(1+c+n)^(abs_(b)+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,c+1) + sign(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(b,?a),X(1),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,d,binom_(d+k-1-jjj,k-1)*sign(k)*den(-c)^(d+k-jjj)*(GG(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(d+k-1-jjj,d-1)*sign(k-jjj)*den(-c)^(d+k-jjj)*GG(R,X,RU(b,?a),RL(?e),jjj,n,c));
* Case c<-2, p_1<0 and q_1<0 (sommetjes equation 7.382)
id GG(R,X,RU(b?{<0},?a),RL(d?{<0},?e),k?{>-1},n?,c?{<-2}) = - GG(R,X,RU(b,?a),RL(d,?e),k,n,c+1)
      + S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))*den(n)*den(n+c)^k
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(1+c+n)^(abs_(b)+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,c+1) + sign(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1,nargs_(?a))))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU(d,?e),RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(b,?a),X(1),jj,nargs_(?a))) - den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(GG(R,X,RU(b,?a),RL(d,?e),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(b,?a),X(1),1,nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(d,?e),RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(d,?e),X(1),n-jj,nargs_(?e))*S(R(?a),X(),jj,nargs_(?a))) + den(n)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL(d,?e),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(d,?e),X(1),n-1,nargs_(?e))*S(R(?a),X(),1,nargs_(?a))))
      + sum_(jjj,1,abs_(d),binom_(abs_(d)+k-1-jjj,k-1)*sign(k)*den(-c)^(abs_(d)+k-jjj)*(TT(R,X,RU(b,?a),RL(?e),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?e),X(),jj,nargs_(?e))*S(R(b,?a),X(1),n-jj,nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(d)+k-1-jjj,abs_(d)-1)*sign(k-jjj)*den(-c)^(abs_(d)+k-jjj)*TT(R,X,RU(b,?a),RL(?e),jjj,n,c));
*--#]

if ((match(once,GG(R,X,RU(b?,?a),RL(d?,?e),k?{>-1},n?,c?{>1})))||(match(once,TT(R,X,RU(b?,?a),RL(d?,?e),k?{>-1},n?,c?{>1})))||(match(once,GG(R,X,RU(b?,?a),RL(d?,?e),k?{>-1},n?,c?{<0})))||(match(once,TT(R,X,RU(b?,?a),RL(d?,?e),k?{>-1},n?,c?{<0}))));
    redefine i "0";
endif;
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
id invbino(n?int_,j?int_) = 1/binom_(n,j);
.sort
#enddo

*--#]

*--#[ c=1

*--#[ Sign altering
* Case c=1 and q_1>=0 (sommetjes equation 7.44)
id TT(R,X,RU(b?,?a),RL(d?{>=0},?x),k?{>-1},n?,1) = -(n+1)*TT(R,X,RU(b,?a),RL(d,?x),k+1,n+1,0) + (n+1)*TT(R,X,RU(b,?a),RL(?x),d+k+1,n+1,0);
* Case c=1 and q_1<0 (sommetjes equation 7.45)
id TT(R,X,RU(b?,?a),RL(d?{<0},?x),k?{>-1},n?,1) = -(n+1)*TT(R,X,RU(b,?a),RL(d,?x),k+1,n+1,0) + (n+1)*GG(R,X,RU(b,?a),RL(?x),abs_(d)+k+1,n+1,0);
*--#]

*--#[ Fixed sign
* Case c=1 and q_1>=0 (sommetjes equation 7.363)
id GG(R,X,RU(b?,?a),RL(d?{>=0},?x),k?{>-1},n?,1) = (n+1)*GG(R,X,RU(b,?a),RL(d,?x),k+1,n+1,0) - (n+1)*GG(R,X,RU(b,?a),RL(?x),d+k+1,n+1,0);
* Case c=1 and q_1<0 (sommetjes equation 7.364) 
id GG(R,X,RU(b?,?a),RL(d?{<0},?x),k?{>-1},n?,1) = (n+1)*GG(R,X,RU(b,?a),RL(d,?x),k+1,n+1,0) - (n+1)*TT(R,X,RU(b,?a),RL(?x),abs_(d)+k+1,n+1,0);
*--#]

*--#]

*--#]

.sort

*--#[ Synchronization of invbino sums containing 1 S-sum

*--#[ c>1 and c<0

#do i = 1,1

*--#[ Upper indices

*--#[ Sign altering
* Upper indices with c>1 (sommetjes equation 7.36)
id TT(R,X,RU(b?,?a),RL,k?{>-1},n?,c?{>1}) = -(n+1)*den(c-1)^(k)*TT(R,X,RU(b,?a),RL,1,n+1,0)
      + sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*TT(R,X,RU(b,?a),RL,jjj,n+1,c-1))
      - den(c)^k*S(R(b,?a),X(1),n)*g(nargs_(?a));
* Upper indices with c=-1 and p_1>=0 (sommetjes equation 7.39)
id TT(R,X,RU(b?{>=0},?a),RL,k?{>-1},n?,-1) = TT(R,X,RU(b,?a),RL,k,n,0)
      + den(n)*sign(n)*den(n-1)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(n)^(b+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n)^(b+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU,RL(b,?a),1,n,0) + den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(k+1-jjj)*(TT(R,X,RU(b,?a),RL,jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(n)^(b+1+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c=-1 and p_1<0 (sommetjes equation 7.40)
id TT(R,X,RU(b?{<0},?a),RL,k?{>-1},n?,-1) = TT(R,X,RU(b,?a),RL,k,n,0)
      + den(n)*sign(n)*den(n-1)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU,RL(b,?a),1,n,0) + den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(k+1-jjj)*(TT(R,X,RU(b,?a),RL,jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c=-2 and p_1>=0 (sommetjes equation 7.39)
id TT(R,X,RU(b?{>=0},?a),RL,k?{>-1},n?,-2) = TT(R,X,RU(b,?a),RL,k,n,-1)
      + den(n)*sign(n)*den(n-2)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(n-1)^(b+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - den(n)*sign(n-1)*S(R(?a),X(),n-1)*g(nargs_(?a))*den(n-1)^(jjj) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n-1)^(b+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU,RL(b,?a),1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)) + den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(k+1-jjj)*(TT(R,X,RU(b,?a),RL,jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(n-1)^(b+1+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(?a),X(),n-1)*g(nargs_(?a)) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n-1)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c=-2 and p_1<0 (sommetjes equation 7.40)
id TT(R,X,RU(b?{<0},?a),RL,k?{>-1},n?,-2) = TT(R,X,RU(b,?a),RL,k,n,-1)
      + den(n)*sign(n)*den(n-2)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*S(R(?a),X(),n-1)*g(nargs_(?a))*den(n-1)^(jjj) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU,RL(b,?a),1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)) + den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(k+1-jjj)*(TT(R,X,RU(b,?a),RL,jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(?a),X(),n-1)*g(nargs_(?a)) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c<-2 and p_1>=0 (sommetjes equation 7.39)
id TT(R,X,RU(b?{>=0},?a),RL,k?{>-1},n?,c?{<-2}) = TT(R,X,RU(b,?a),RL,k,n,c+1)
      + den(n)*sign(n)*den(n+c)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      - sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(n)*den(1+c+n)^(b+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*S(R(?a),X(),jj)*g(nargs_(?a))*den(jj)^(jjj)) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(1+c+n)^(b+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU,RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(b,?a),X(1),jj)*g(nargs_(?a))) + den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(k+1-jjj)*(TT(R,X,RU(b,?a),RL,jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      + sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*sign(n)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a))) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c<-2 and p_1<0 (sommetjes equation 7.40)
id TT(R,X,RU(b?{<0},?a),RL,k?{>-1},n?,c?{<-2}) = TT(R,X,RU(b,?a),RL,k,n,c+1)
      + den(n)*sign(n)*den(n+c)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      - sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*S(R(?a),X(),jj)*g(nargs_(?a))*den(jj)^(jjj)) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU,RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(b,?a),X(1),jj)*g(nargs_(?a))) + den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(k+1-jjj)*(TT(R,X,RU(b,?a),RL,jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a))) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
*--#]
.sort
*--#[ Fixed sign
* Upper indices with c>1 (sommetjes equation 7.355)
id GG(R,X,RU(b?,?a),RL,k?{>-1},n?,c?{>1}) = (n+1)*den(c-1)^(k)*GG(R,X,RU(b,?a),RL,1,n+1,0)
      - sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*GG(R,X,RU(b,?a),RL,jjj,n+1,c-1))
      - den(c)^k*S(R(b,?a),X(1),n)*g(nargs_(?a));
* Upper indices with c=-1 and p_1>=0 (sommetjes equation 7.367)
id GG(R,X,RU(b?{>=0},?a),RL,k?{>-1},n?,-1) = - GG(R,X,RU(b,?a),RL,k,n,0)
      + den(n)*den(n-1)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(n)^(b+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n)^(b+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      + (n+1)*den(n)^k*(GG(R,X,RU,RL(b,?a),1,n,0) - den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(k+1-jjj)*(GG(R,X,RU(b,?a),RL,jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(n)^(b+1+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c=-1 and p_1<0 (sommetjes equation 7.368)
id GG(R,X,RU(b?{<0},?a),RL,k?{>-1},n?,-1) = - GG(R,X,RU(b,?a),RL,k,n,0)
      + den(n)*den(n-1)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(n)^(abs_(b)+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      + (n+1)*den(n)^k*(GG(R,X,RU,RL(b,?a),1,n,0) - den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(k+1-jjj)*(GG(R,X,RU(b,?a),RL,jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c=-2 and p_1>=0 (sommetjes equation 7.367)
id GG(R,X,RU(b?{>=0},?a),RL,k?{>-1},n?,-2) = - GG(R,X,RU(b,?a),RL,k,n,-1)
      + den(n)*den(n-2)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(n-1)^(b+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*S(R(?a),X(),n-1)*g(nargs_(?a))*den(n-1)^(jjj) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(n-1)^(b+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      + (n+1)*den(n-1)^k*(GG(R,X,RU,RL(b,?a),1,n,0) - den(n)*den(n-1)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)) - den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(k+1-jjj)*(GG(R,X,RU(b,?a),RL,jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(n-1)^(b+1+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(?a),X(),n-1)*g(nargs_(?a)) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(n-1)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c=-2 and p_1<0 (sommetjes equation 7.368)
id GG(R,X,RU(b?{<0},?a),RL,k?{>-1},n?,-2) = - GG(R,X,RU(b,?a),RL,k,n,-1)
      + den(n)*den(n-2)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(n-1)^(abs_(b)+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - den(n)*sign(n-1)*S(R(?a),X(),n-1)*g(nargs_(?a))*den(n-1)^(jjj) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(n-1)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      + (n+1)*den(n-1)^k*(GG(R,X,RU,RL(b,?a),1,n,0) - den(n)*den(n-1)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)) - den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(k+1-jjj)*(GG(R,X,RU(b,?a),RL,jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - den(n)*sign(n-1)*den(n-1)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(n-1)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c<-2 and p_1>=0 (sommetjes equation 7.367)
id GG(R,X,RU(b?{>=0},?a),RL,k?{>-1},n?,c?{<-2}) = - GG(R,X,RU(b,?a),RL,k,n,c+1)
      + den(n)*den(n+c)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*den(1+c+n)^(b+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*S(R(?a),X(),jj)*g(nargs_(?a))*den(jj)^(jjj)) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*den(1+c+n)^(b+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU,RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(b,?a),X(1),jj)*g(nargs_(?a))) - den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(k+1-jjj)*(GG(R,X,RU(b,?a),RL,jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      - sum_(jjj,1,b+1,binom_(b+k-jjj,k-1)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a))) - den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(b+k-jjj,b)*(n+1)*den(1+c+n)^(b+1+k-jjj)*(GG(R,X,RU(?a),RL,jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
* Upper indices with c<-2 and p_1<0 (sommetjes equation 7.368)
id GG(R,X,RU(b?{<0},?a),RL,k?{>-1},n?,c?{<-2}) = - GG(R,X,RU(b,?a),RL,k,n,c+1)
      + den(n)*den(n+c)^k*S(R(b,?a),X(1),1)*g(nargs_(?a))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*den(1+c+n)^(abs_(b)+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*S(R(?a),X(),jj)*g(nargs_(?a))*den(jj)^(jjj)) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(n)*den(1+c+n)^(abs_(b)+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU,RL(b,?a),1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(b,?a),X(1),jj)*g(nargs_(?a))) - den(n)*S(R(b,?a),X(1),1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(k+1-jjj)*(GG(R,X,RU(b,?a),RL,jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),1)*g(nargs_(?a))))
      - sum_(jjj,1,abs_(b)+1,binom_(abs_(b)+k-jjj,k-1)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a))) + den(n)*S(R(?a),X(),1)*g(nargs_(?a))))
      - sum_(jjj,1,k,binom_(abs_(b)+k-jjj,abs_(b))*sign(n)*(n+1)*den(1+c+n)^(abs_(b)+1+k-jjj)*(TT(R,X,RU(?a),RL,jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(?a),X(),1)*g(nargs_(?a))));
*--#]

*--#]
.sort
*--#[ Lower indices

*--#[ Sign altering
* Lower indices with c>1 and q_1>=0 (sommetjes equation 7.38)
id TT(R,X,RU,RL(d?{>=0},?x),k?{>-1},n?,c?{>1}) = -(n+1)*den(c-1)^(k)*TT(R,X,RU,RL(d,?x),1,n+1,0)
      + sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*TT(R,X,RU,RL(d,?x),jjj,n+1,c-1))
      - sum_(jjj,1,d+1,binom_(d+k-jjj,k-1)*(n+1)*sign(d-jjj)*den(c-1)^(d+k-jjj+1)*TT(R,X,RU,RL(?x),jjj,n+1,0))
      - sum_(jjj,1,k,binom_(d+k-jjj,d)*(n+1)*sign(d)*den(c-1)^(d+k-jjj+1)*TT(R,X,RU,RL(?x),jjj,n+1,c-1));
* Lower indices with c>1 and q_1<0 (sommetjes equation 7.39) 
id TT(R,X,RU,RL(d?{<0},?x),k?{>-1},n?,c?{>1}) = -(n+1)*den(c-1)^(k)*TT(R,X,RU,RL(d,?x),1,n+1,0)
      + sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*TT(R,X,RU,RL(d,?x),jjj,n+1,c-1))
      - sum_(jjj,1,abs_(d)+1,binom_(abs_(d)+k-jjj,k-1)*(n+1)*sign(abs_(d)-jjj)*den(c-1)^(abs_(d)+k-jjj+1)*GG(R,X,RU,RL(?x),jjj,n+1,0))
      - sum_(jjj,1,k,binom_(abs_(d)+k-jjj,abs_(d))*(n+1)*sign(abs_(d))*den(c-1)^(abs_(d)+k-jjj+1)*GG(R,X,RU,RL(?x),jjj,n+1,c-1));
* Lower indices with c=-1 and q_1>=0 (sommetjes equation 7.45)
id TT(R,X,RU,RL(b?{>=0},?a),k?{>-1},n?,-1) = TT(R,X,RU,RL(b,?a),k,n,0)
      + sign(n)*den(n)*den(n-1)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU(b,?a),RL,1,n,0) + den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(TT(R,X,RU,RL(b,?a),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(k)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*sign(k-jjj)*TT(R,X,RU,RL(?a),jjj,n,-1));
* Lower indices with c=-1 and q_1<0 (sommetjes equation 7.46)
id TT(R,X,RU,RL(b?{<0},?a),k?{>-1},n?,-1) = TT(R,X,RU,RL(b,?a),k,n,0)
      + sign(n)*den(n)*den(n-1)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      - sign(n)*(n+1)*den(n)^k*(TT(R,X,RU(b,?a),RL,1,n,0) + den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(TT(R,X,RU,RL(b,?a),jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(k)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(k-jjj)*GG(R,X,RU,RL(?a),jjj,n,-1));
* Lower indices with c=-2 and q_1>=0 (sommetjes equation 7.45)
id TT(R,X,RU,RL(b?{>=0},?a),k?{>-1},n?,-2) = TT(R,X,RU,RL(b,?a),k,n,-1)
      + sign(n)*den(n)*den(n-2)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU(b,?a),RL,1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(b,?a),X(1),1)*g(nargs_(?a)) + den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(TT(R,X,RU,RL(b,?a),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(k)*den(2)^(b+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*sign(k-jjj)*den(2)^(b+k-jjj)*TT(R,X,RU,RL(?a),jjj,n,-2));
* Lower indices with c=-2 and q_1<0 (sommetjes equation 7.46)
id TT(R,X,RU,RL(b?{<0},?a),k?{>-1},n?,-2) = TT(R,X,RU,RL(b,?a),k,n,-1)
      + sign(n)*den(n)*den(n-2)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      - sign(n)*(n+1)*den(n-1)^k*(TT(R,X,RU(b,?a),RL,1,n,0) - den(n)*sign(n-1)*den(n-1)*S(R(b,?a),X(1),1)*g(nargs_(?a)) + den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(TT(R,X,RU,RL(b,?a),jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(k)*den(2)^(abs_(b)+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(k-jjj)*den(2)^(abs_(b)+k-jjj)*GG(R,X,RU,RL(?a),jjj,n,-2));
* Lower indices with c<-2 and q_1>=0 (sommetjes equation 7.45)
id TT(R,X,RU,RL(b?{>=0},?a),k?{>-1},n?,c?{<-2}) = TT(R,X,RU,RL(b,?a),k,n,c+1)
      + sign(n)*den(n)*den(n+c)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU(b,?a),RL,1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(b,?a),X(1),n-jj)*g(nargs_(?a))) + den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(TT(R,X,RU,RL(b,?a),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(k)*den(-c)^(b+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*sign(k-jjj)*den(-c)^(b+k-jjj)*TT(R,X,RU,RL(?a),jjj,n,c));
* Lower indices with c<-2 and q_1<0 (sommetjes equation 7.46)
id TT(R,X,RU,RL(b?{<0},?a),k?{>-1},n?,c?{<-2}) = TT(R,X,RU,RL(b,?a),k,n,c+1)
      + sign(n)*den(n)*den(n+c)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      - sign(n)*(n+1)*den(1+c+n)^k*(TT(R,X,RU(b,?a),RL,1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)*S(R(b,?a),X(1),n-jj)*g(nargs_(?a))) + den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(TT(R,X,RU,RL(b,?a),jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(k)*den(-c)^(abs_(b)+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(k-jjj)*den(-c)^(abs_(b)+k-jjj)*GG(R,X,RU,RL(?a),jjj,n,c));      
*--#]
.sort
*--#[ Fixed sign
* Lower indices with c>1 and q_1>=0 (sommetjes equation 7.357)
id GG(R,X,RU,RL(d?{>=0},?x),k?{>-1},n?,c?{>1}) = (n+1)*den(c-1)^(k)*GG(R,X,RU,RL(d,?x),1,n+1,0)
        - sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*GG(R,X,RU,RL(d,?x),jjj,n+1,c-1))
        + sum_(jjj,1,d+1,binom_(d+k-jjj,k-1)*(n+1)*sign(d-jjj)*den(c-1)^(d+k-jjj+1)*GG(R,X,RU,RL(?x),jjj,n+1,0))
        + sum_(jjj,1,k,binom_(d+k-jjj,d)*(n+1)*sign(d)*den(c-1)^(d+k-jjj+1)*GG(R,X,RU,RL(?x),jjj,n+1,c-1));
* Lower indices with c>1 and q_1<0 (sommetjes equation 7.358) 
id GG(R,X,RU,RL(d?{<0},?x),k?{>-1},n?,c?{>1}) = (n+1)*den(c-1)^(k)*GG(R,X,RU,RL(d,?x),1,n+1,0)
        - sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*GG(R,X,RU,RL(d,?x),jjj,n+1,c-1))
        + sum_(jjj,1,abs_(d)+1,binom_(abs_(d)+k-jjj,k-1)*(n+1)*sign(abs_(d)-jjj)*den(c-1)^(abs_(d)+k-jjj+1)*TT(R,X,RU,RL(?x),jjj,n+1,0))
        + sum_(jjj,1,k,binom_(abs_(d)+k-jjj,abs_(d))*(n+1)*sign(abs_(d))*den(c-1)^(abs_(d)+k-jjj+1)*TT(R,X,RU,RL(?x),jjj,n+1,c-1));
* Lower indices with c=-1 and q_1>=0 (sommetjes equation 7.373)
id GG(R,X,RU,RL(b?{>=0},?a),k?{>-1},n?,-1) = - GG(R,X,RU,RL(b,?a),k,n,0)
      + den(n)*den(n-1)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      + (n+1)*den(n)^k*(GG(R,X,RU(b,?a),RL,1,n,0) - den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(GG(R,X,RU,RL(b,?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(k)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*sign(k-jjj)*GG(R,X,RU,RL(?a),jjj,n,-1));
* Lower indices with c=-1 and q_1<0 (sommetjes equation 7.374)
id GG(R,X,RU,RL(b?{<0},?a),k?{>-1},n?,-1) = - GG(R,X,RU,RL(b,?a),k,n,0)
      + den(n)*den(n-1)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      + (n+1)*den(n)^k*(GG(R,X,RU(b,?a),RL,1,n,0) - den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(GG(R,X,RU,RL(b,?a),jjj,n,0) - den(n)*den(n-1)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(k)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,1,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(k-jjj)*TT(R,X,RU,RL(?a),jjj,n,-1));
* Lower indices with c=-2 and q_1>=0 (sommetjes equation 7.373)
id GG(R,X,RU,RL(b?{>=0},?a),k?{>-1},n?,-2) = - GG(R,X,RU,RL(b,?a),k,n,-1)
      + den(n)*den(n-2)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      + (n+1)*den(n-1)^k*(GG(R,X,RU(b,?a),RL,1,n,0) - den(n)*den(n-1)*S(R(b,?a),X(1),1)*g(nargs_(?a)) - den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(GG(R,X,RU,RL(b,?a),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(k)*den(2)^(b+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*sign(k-jjj)*den(2)^(b+k-jjj)*GG(R,X,RU,RL(?a),jjj,n,-2));
* Lower indices with c=-2 and q_1<0 (sommetjes equation 7.374)
id GG(R,X,RU,RL(b?{<0},?a),k?{>-1},n?,-2) = - GG(R,X,RU,RL(b,?a),k,n,-1)
      + den(n)*den(n-2)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      + (n+1)*den(n-1)^k*(GG(R,X,RU(b,?a),RL,1,n,0) - den(n)*den(n-1)*S(R(b,?a),X(1),1)*g(nargs_(?a)) - den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(GG(R,X,RU,RL(b,?a),jjj,n,-1) - den(n)*den(n-2)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(k)*den(2)^(abs_(b)+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,2,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(k-jjj)*den(2)^(abs_(b)+k-jjj)*TT(R,X,RU,RL(?a),jjj,n,-2));
* Lower indices with c<-2 and q_1>=0 (sommetjes equation 7.373)
id GG(R,X,RU,RL(b?{>=0},?a),k?{>-1},n?,c?{<-2}) = - GG(R,X,RU,RL(b,?a),k,n,c+1)
      + den(n)*den(n+c)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU(b,?a),RL,1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(b,?a),X(1),n-jj)*g(nargs_(?a))) - den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(GG(R,X,RU,RL(b,?a),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,b,binom_(b+k-1-jjj,k-1)*sign(k)*den(-c)^(b+k-jjj)*(GG(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(b+k-1-jjj,b-1)*sign(k-jjj)*den(-c)^(b+k-jjj)*GG(R,X,RU,RL(?a),jjj,n,c));
* Lower indices with c<-2 and q_1<0 (sommetjes equation 7.374)
id GG(R,X,RU,RL(b?{<0},?a),k?{>-1},n?,c?{<-2}) = - GG(R,X,RU,RL(b,?a),k,n,c+1)
      + den(n)*den(n+c)^k*S(R(b,?a),X(1),n-1)*g(nargs_(?a))
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU(b,?a),RL,1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)*S(R(b,?a),X(1),n-jj)*g(nargs_(?a))) - den(n)*S(R(b,?a),X(1),n-1)*g(nargs_(?a)))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(GG(R,X,RU,RL(b,?a),jjj,n,c+1) - den(n)*den(n+c)^(jjj)*S(R(b,?a),X(1),n-1)*g(nargs_(?a))))
      + sum_(jjj,1,abs_(b),binom_(abs_(b)+k-1-jjj,k-1)*sign(k)*den(-c)^(abs_(b)+k-jjj)*(TT(R,X,RU,RL(?a),jjj,n,0) - sum_(jj,1,-c,invbino(n,jj)*sign(jj)*den(jj)^(jjj)*S(R(?a),X(),jj)*g(nargs_(?a)))))
      + sum_(jjj,1,k,binom_(abs_(b)+k-1-jjj,abs_(b)-1)*sign(k-jjj)*den(-c)^(abs_(b)+k-jjj)*TT(R,X,RU,RL(?a),jjj,n,c));
*--#]

*--#]

if ((match(once,GG(R,X,RU,RL(d?,?x),k?{>-1},n?,c?{>1})))||(match(once,TT(R,X,RU,RL(d?,?x),k?{>-1},n?,c?{>1})))||(match(once,GG(R,X,RU(d?,?x),RL,k?{>-1},n?,c?{>1})))||(match(once,TT(R,X,RU(d?,?x),RL,k?{>-1},n?,c?{>1})))||(match(once,GG(R,X,RU,RL(d?,?x),k?{>-1},n?,c?{<0})))||(match(once,TT(R,X,RU,RL(d?,?x),k?{>-1},n?,c?{<0})))||(match(once,GG(R,X,RU(d?,?x),RL,k?{>-1},n?,c?{<0})))||(match(once,TT(R,X,RU(d?,?x),RL,k?{>-1},n?,c?{<0}))));
    redefine i "0";
endif;
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
id invbino(n?int_,j?int_) = 1/binom_(n,j);
.sort
#enddo

*--#]

*--#[ c=1

*--#[ Sign altering
* Upper indices with c=1 (sommetjes equation 7.37)
id TT(R,X,RU(b?,?a),RL,k?{>-1},n?,1) = -(n+1)*TT(R,X,RU(b,?a),RL,k+1,n+1,0) - S(R(b,?a),X(1),n)*g(nargs_(?a));
* Lower indices with c=1 and q_1>=0 (sommetjes equation 7.40)
id TT(R,X,RU,RL(d?{>=0},?x),k?{>-1},n?,1) = -(n+1)*TT(R,X,RU,RL(d,?x),k+1,n+1,0) + (n+1)*TT(R,X,RU,RL(?x),d+k+1,n+1,0);
* Lower indices with c=1 and q_1<0 (sommetjes equation 7.41) 
id TT(R,X,RU,RL(d?{<0},?x),k?{>-1},n?,1) = -(n+1)*TT(R,X,RU,RL(d,?x),k+1,n+1,0) + (n+1)*GG(R,X,RU,RL(?x),abs_(d)+k+1,n+1,0);
*--#]

*--#[ Fixed sign
* Upper indices with c=1 (sommetjes equation 7.356)
id GG(R,X,RU(b?,?a),RL,k?{>-1},n?,1) = (n+1)*GG(R,X,RU(b,?a),RL,k+1,n+1,0) - S(R(b,?a),X(1),n)*g(nargs_(?a));
* Lower indices with c=1 and q_1>=0 (sommetjes equation 7.359)
id GG(R,X,RU,RL(d?{>=0},?x),k?{>-1},n?,1) = (n+1)*GG(R,X,RU,RL(d,?x),k+1,n+1,0) - (n+1)*GG(R,X,RU,RL(?x),d+k+1,n+1,0);
* Lower indices with c=1 and q_1<0 (sommetjes equation 7.360) 
id GG(R,X,RU,RL(d?{<0},?x),k?{>-1},n?,1) = (n+1)*GG(R,X,RU,RL(d,?x),k+1,n+1,0) - (n+1)*TT(R,X,RU,RL(?x),abs_(d)+k+1,n+1,0);
*--#]

*--#]

*--#]

.sort

*--#[ Synchronization of invbino sums containing 0 S-sums

*--#[ c>1 and c<0

#do i = 1,1

*--#[ Sign altering
* Case c>1 (sommetjes equation 7.34)
id TT(R,X,RU,RL,k?{>-1},n?,c?{>1}) = -(n+1)*den(c-1)^k*TT(R,X,RU,RL,1,n+1,0)
      + sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*TT(R,X,RU,RL,jjj,n+1,c-1)) 
      - den(c)^k;
* Case c=-1 (sommetjes equation 7.36)
id TT(R,X,RU,RL,k?{>-1},n?,-1) = TT(R,X,RU,RL,k,n,0)
      + sign(n)*(n+1)*den(n)^k*(-TT(R,X,RU,RL,1,n,0) - den(n))
      - sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(TT(R,X,RU,RL,jjj,n,0) + sign(n)*den(n)*den(n-1)^(jjj)))
      + sign(n)*den(n)*den(n-1)^k;
* Case c=-2 (sommetjes equation 7.36)
id TT(R,X,RU,RL,k?{>-1},n?,-2) = TT(R,X,RU,RL,k,n,-1)
      + sign(n)*(n+1)*den(n-1)^k*(-TT(R,X,RU,RL,1,n,0) + den(n)*sign(n-1)*den(n-1) - den(n))
      - sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(TT(R,X,RU,RL,jjj,n,-1) + sign(n)*den(n)*den(n-2)^(jjj)))
      + sign(n)*den(n)*den(n-2)^k;
* Case c<-2 (sommetjes equation 7.36)
id TT(R,X,RU,RL,k?{>-1},n?,c?{<-2}) = TT(R,X,RU,RL,k,n,c+1)
      + sign(n)*(n+1)*den(1+c+n)^k*(-TT(R,X,RU,RL,1,n,0) + sum(jj,n+c+1,n-1,invbino(n,jj)*sign(jj)*den(jj)) - den(n))
      - sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(TT(R,X,RU,RL,jjj,n,c+1) + sign(n)*den(n)*den(n+c)^(jjj)))
      + sign(n)*den(n)*den(n+c)^k;
*--#]

*--#[ Fixed sign
* Case c>1 (sommetjes equation 7.353)
id GG(R,X,RU,RL,k?{>-1},n?,c?{>1}) = (n+1)*den(c-1)^k*GG(R,X,RU,RL,1,n+1,0)
        - sum_(jjj,1,k,(n+1)*den(c-1)^(k+1-jjj)*GG(R,X,RU,RL,jjj,n+1,c-1)) 
        - den(c)^k;
* Case c=-1 (sommetjes equation 7.364)
id GG(R,X,RU,RL,k?{>-1},n?,-1) = -GG(R,X,RU,RL,k,n,0)
      + den(n)*den(n-1)^k
      + (n+1)*den(n)^k*(GG(R,X,RU,RL,1,n,0) - den(n))
      + sum_(jjj,1,k,(n+1)*den(n)^(1+k-jjj)*(GG(R,X,RU,RL,jjj,n,0) - den(n)*den(n-1)^(jjj)));
* Case c=-2 (sommetjes equation 7.364)
id GG(R,X,RU,RL,k?{>-1},n?,-2) = -GG(R,X,RU,RL,k,n,-1)
      + den(n)*den(n-2)^k
      + (n+1)*den(n-1)^k*(GG(R,X,RU,RL,1,n,0) - den(n)*den(n-1) - den(n))
      + sum_(jjj,1,k,(n+1)*den(n-1)^(1+k-jjj)*(GG(R,X,RU,RL,jjj,n,-1) - den(n)*den(n-2)^(jjj)));
* Case c<-2 (sommetjes equation 7.364)
id GG(R,X,RU,RL,k?{>-1},n?,c?{<-2}) = -GG(R,X,RU,RL,k,n,c+1)
      + den(n)*den(n+c)^k
      + (n+1)*den(1+c+n)^k*(GG(R,X,RU,RL,1,n,0) - sum(jj,n+c+1,n-1,invbino(n,jj)*den(jj)) - den(n))
      + sum_(jjj,1,k,(n+1)*den(1+c+n)^(1+k-jjj)*(GG(R,X,RU,RL,jjj,n,c+1) - den(n)*den(n+c)^(jjj)));
*--#]

if ((match(once,GG(R,X,RU,RL,k?{>-1},n?,c?{<0})))||(match(once,TT(R,X,RU,RL,k?{>-1},n?,c?{<0})))||(match(once,GG(R,X,RU,RL,k?{>-1},n?,c?{>1})))||(match(once,TT(R,X,RU,RL,k?{>-1},n?,c?{>1}))));
    redefine i "0";
endif;
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
id invbino(n?int_,j?int_) = 1/binom_(n,j);
.sort
#enddo

*--#]

*--#[ c=1

*--#[ Sign altering
* Case c=1 (sommetjes equation 7.35)
id TT(R,X,RU,RL,k?{>-1},n?,1) = -(n+1)*TT(R,X,RU,RL,k+1,n+1,0) - 1;
*--#]

*--#[ Fixed sign
* Case c=1 (sommetjes equation 7.354)
id GG(R,X,RU,RL,k?{>-1},n?,1) = (n+1)*GG(R,X,RU,RL,k+1,n+1,0) - 1;
*--#]

*--#]

*--#]

id sum(jj,a?{>0},b?{>0},?c) = sum_(jj,a,b,?c);
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
id invbino(n?int_,j?int_) = 1/binom_(n,j);
.sort

*--#[ Fixing the length of the X-vector in the S-sums that appear as products

repeat id S(R(?a),X(?b),n?,c?{>0}) = S(R(?a),X(?b,1),n,c-1);
id S(R(?a),X(?b),n?,0) = S(R(?a),X(?b),n);

*--#]

*
* Final step to make the link between the procedure for solving the inverse binomial sums
*
id TT(?a,0) = TT(?a);
id GG(?a,0) = GG(?a);
#endprocedure
*--#]

*--#[ Interface
#procedure Interface
*
* Procedure for identifying the inverse binomial sums and checking whether they meet the requirements to be solved.
* 
* First we identify the (1/j+c)^k term
.sort
Splitarg, den, S;
id den(c?,-j) = (-1)*den(-c,j);
id den(c?,j) = den(c,j,1);
repeat id den(c?,j,m?{>0})*den(c?,j,n?{>0}) = den(c,j,m+n);
id den(c?int_,n) = den(n+c);
id den(c?int_,-n) = den(-n+c);
id S(R(?a),c?int_,n) = S(R(?a),n+c);
id S(R(?a),c?int_,-n) = S(R(?a),-n+c);

*--#[ Checks
* Here we check if the boundaries of the inverse binomial sum don't overlap each other
id sum(j,a?{>0},b?{>0}) = sum(j,a,b)*g(b-a);
if (match(once,g(x?{<0})));
    $check12 = 1;
endif;
.sort
#if ( '$check12' == 1 )
    #write "The limits of your inverse binomial sum overlap. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
id g(x?{>=0}) = 1;
* Here we check if the denominator in the inverse binomial sum contains the right denominator
if ( (match(once,den(c?,j,-n)))||(match(once,den(j,-n)))||(match(once,den(c?,-j,n)))||(match(once,den(-j,n))) );
    $denflip = 1;
endif;
.sort
#if( '$denflip' == 1 )
    #write "There is a denominator in the inverse binomial sum present that still needs to be rewritten into the right form.
    Please see the manual for instructions on how to use the Denflip procedure."
    #terminate
#endif
* Here we check if one of the S-sums in the inverse binomial sum contains 0 as an index
if ( match(once,S(R(?a,0,?b),?j)) );
    $zeroindex = 1;
endif;
.sort
#if( '$zeroindex' == 1 )
    #write "One of the S-sums contained in the inverse binomial sum contains zero as an index. This procedure only works for indices that are not equal to zero. See appendix ???? to see how you can get rid of the 0 index in your S-sum."
    #terminate
#endif
* Here we check if the upper bound of the inverse binomial sum is equal to n-1 and identify the invbino sums with our internal notation
id sum(j,d?,e?)*invbino(n?,j) = sum(j,d,e)*invbino(n,j)*g(n-e);
id g(x?$check1) = g(x);
id sum(j,d?,e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1}) = sum(j,d,e)*invbino(n,j)*den(c,j,k)*g1(d+c-1);
id g1(x?$check3) = g1(x);
*--#]

*--#[ Identification
.sort
#if ( '$check1' == 1 )
    id g(1) = 1;
*   We first identify the inverse binomial sums that have to be synchronized before they can be solved by the invbino procedure
    id sum(j,1,e?)*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),k,n,c);
    id sum(j,1,e?)*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*S(R(?a),n?{>1},-j)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),k,n,c);
    id sum(j,1,e?)*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j) = TT(R,X,RU(?a),RL,k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = TT(R,X,RU(?a),RL,k,n,c);
    id sum(j,1,e?)*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*S(R(?a),n?{>1},-j) = GG(R,X,RU(?a),RL,k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?) = GG(R,X,RU(?a),RL,k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),j) = TT(R,X,RU,RL(?a),k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),j) = GG(R,X,RU,RL(?a),k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = TT(R,X,RU,RL,k,n,c);
    id sum(j,1,e?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = GG(R,X,RU,RL,k,n,c);
    #if ( '$check3' == 0)
      id g1(0) = 1;
      id sum(j,d?{>0},e?)*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*S(R(?a),n?{>1},-j)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j) = TT(R,X,RU(?a),RL,k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = TT(R,X,RU(?a),RL,k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*S(R(?a),n?{>1},-j) = GG(R,X,RU(?a),RL,k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?) = GG(R,X,RU(?a),RL,k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),j) = TT(R,X,RU,RL(?a),k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),j) = GG(R,X,RU,RL(?a),k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j) = TT(R,X,RU,RL,k,n,c);
      id sum(j,d?{>0},e?)*invbino(n?,j)*den(c?{<0},j,k?{>-1}) = GG(R,X,RU,RL,k,n,c);
    #else
      #write "The inverse binomial sum has not been written down in the correct way. Please see the manual for instructions on how to write down your inverse binomial sum as input."
      #terminate
    #endif
    #call Synchronization
*   We are now ready to identify the inverse binomial sums that can directly be solved by the invbino procedure
    id den(-j) = (-den(j));
    id den(j) = den(j,1);
    repeat id den(j,m?{>0})*den(j,n?{>0}) = den(j,m+n);
    id sum(j,1,e?)*invbino(n?{>1},j)*den(j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),k,n);
    id sum(j,1,e?)*invbino(n?{>1},j)*den(j,k?{>-1})*S(R(?a),n?{>1},-j)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),k,n);
    id sum(j,1,e?)*invbino(n?{>1},j)*den(j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j) = TT(R,X,RU(?a),RL,k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = TT(R,X,RU(?a),RL,k,n);
    id sum(j,1,e?)*invbino(n?{>1},j)*den(j,k?{>-1})*S(R(?a),n?{>1},-j) = GG(R,X,RU(?a),RL,k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?) = GG(R,X,RU(?a),RL,k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),j) = TT(R,X,RU,RL(?a),k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),j) = GG(R,X,RU,RL(?a),k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1})*sign(j) = TT(R,X,RU,RL,k,n);
    id sum(j,1,e?)*invbino(n?,j)*den(j,k?{>-1}) = GG(R,X,RU,RL,k,n);
    id sum(j,1,e?)*invbino(n?{>1},j)*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),0,n);
    id sum(j,1,e?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = TT(R,X,RU(?a),RL(?b),0,n);
    id sum(j,1,e?)*invbino(n?{>1},j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),0,n);
    id sum(j,1,e?)*invbino(n?,j)*S(R(?a),-j,n?)*S(R(?b),j) = GG(R,X,RU(?a),RL(?b),0,n);
    id sum(j,1,e?)*invbino(n?{>1},j)*sign(j)*S(R(?a),n?{>1},-j) = TT(R,X,RU(?a),RL,0,n);
    id sum(j,1,e?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?) = TT(R,X,RU(?a),RL,0,n);
    id sum(j,1,e?)*invbino(n?{>1},j)*S(R(?a),n?{>1},-j) = GG(R,X,RU(?a),RL,0,n);
    id sum(j,1,e?)*invbino(n?,j)*S(R(?a),-j,n?) = GG(R,X,RU(?a),RL,0,n);
    id sum(j,1,e?)*invbino(n?,j)*sign(j)*S(R(?a),j) = TT(R,X,RU,RL(?a),0,n);
    id sum(j,1,e?)*invbino(n?,j)*S(R(?a),j) = GG(R,X,RU,RL(?a),0,n);
    id sum(j,1,e?)*invbino(n?,j)*sign(j) = TT(R,X,RU,RL,0,n);
    id sum(j,1,e?)*invbino(n?,j) = GG(R,X,RU,RL,0,n);
#else
#write "The inverse binomial sum has not been written down in the correct way. Please see the manual for instructions on how to write down your inverse binomial sum as input."
#terminate
#endif
*--#]

*--#[ Final check
* Here we check if our interface was able to identify the input as an inverse binomial sum that can be solved by the invbino procedure
if ((match(once,GG(?a)))||(match(once,TT(?b))));
    $check2 = 1;
endif;
.sort
#if ( '$check2' != 1 )
    #write "The inverse binomial sum has not been written down in the correct way. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
*--#]

#endprocedure
*--#]

*--#[ Invbino
#procedure invbino
*
* The procedure for solving an inverse binomial sum with 2 S-sums, 1 S-sum or 0 S-sums. The order of the subprocedures 
* is put in such a way that it first looks for a inverse binomial sum with 2 S-sums, then for an inverse binomial sum with 1 S-sum
* 1 S-sum and then for an inverse binomial sum with 0 S-sums.
*

*--#[ 2 S-sums
#write " The recursion for two S-sums now starts"
*
* These first 256 id statements are there to initiate the recursion if we encounter an inverse binomial sum containing two S-sums. 
*

*--#[k=0

*--#[Sign altering
* Case k=0, p_1>=0 and q_1>=0 (sommetjes equation 7.30)
id TT(R,X,RU(m?{>=0},?a),RL(c?{>=0},?b),0,n?) = (n+1)*den(n+2)*(TT(R,X,RU(m,?a),RL(?b),c,n+1) 
        + sign(n)*TT(R,X,RU(c,?b),RL(?a),m,n+1));
* Case k=0, p_1>=0 and q_1<0 (sommetjes equation 7.31) 
id TT(R,X,RU(m?{>=0},?a),RL(c?{<0},?b),0,n?) = (n+1)*den(n+2)*(GG(R,X,RU(m,?a),RL(?b),abs_(c),n+1) 
        + sign(n)*TT(R,X,RU(c,?b),RL(?a),m,n+1));
* Case k=0, p_1<0 and q_1>=0 (sommetjes equation 7.32) 
id TT(R,X,RU(m?{<0},?a),RL(c?{>=0},?b),0,n?) = (n+1)*den(n+2)*(TT(R,X,RU(m,?a),RL(?b),c,n+1) 
        + sign(n)*GG(R,X,RU(c,?b),RL(?a),abs_(m),n+1));
* Case k=0, p_1<0 and q_1<0 (sommetjes equation 7.33) 
id TT(R,X,RU(m?{<0},?a),RL(c?{<0},?b),0,n?) = (n+1)*den(n+2)*(GG(R,X,RU(m,?a),RL(?b),abs_(c),n+1) 
        + sign(n)*GG(R,X,RU(c,?b),RL(?a),abs_(m),n+1));
*--#]

*--#[Fixed sign
* k=0, s=1, r=1, q_1>1 and p_1>1 (sommetjes equation 7.229) 
id GG(R,X,RU(a?{>1}),RL(b?{>1}),0,n?) = GG(R(a),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(b),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a),RL,b,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL,b,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL,b,n)*den(2)
      +GG(R,X,RU(b),RL,a,n)*den(2)
      +sum_(jjj,1,-1+b,GG(R(1-jjj+b),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,-1+b,GG(R(1-jjj+b),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1>1 and p_1=1 (sommetjes equation 7.230)
id GG(R,X,RU(1),RL(b?{>1}),0,n?) = -GG(R(1+b),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+b),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*b
      -GG(R(1+b),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+b),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n*b
      +GG(R(b),X(2),RU,RL(1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU,RL(1),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(b),X(2),RU,RL,2,n)*den(2)*den(2)^(n+1)
      -GG(R(b),X(2),RU,RL,2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b),RL,1,n)*den(2)
      +GG(R,X,RU(1),RL,b,n)*den(2)
      -sum_(jjj,1,1+b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*b
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n*b;
* k=0, s=1, r=1, q_1>1 and p_1<-1 (sommetjes equation 7.231) 
id GG(R,X,RU(a?{<-1}),RL(b?{>1}),0,n?) = binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*S(R(-1-b-abs_(a)),X(2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*S(R(-1-b-abs_(a)),X(2),n)*n
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*S(R(1+b+abs_(a)),X(2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*S(R(1+b+abs_(a)),X(2),n)*n
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*S(R(-1-b-abs_(a)),X(2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*S(R(-1-b-abs_(a)),X(2),n)*n
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*S(R(1+b+abs_(a)),X(2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*S(R(1+b+abs_(a)),X(2),n)*n
      +GG(R(b),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL,b,n)*den(2)
      +den(2)*den(2)^(n+1)*S(R(1+b+abs_(a)),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(1+b+abs_(a)),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),b),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),b),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU,RL,1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU,RL,1+b,n)*n
      +den(2)*TT(R,X,RU(b),RL,abs_(a),n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1>1 and p_1=-1 (sommetjes equation 7.232)
id GG(R,X,RU(-1),RL(b?{>1}),0,n?) = GG(R(b),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL,b,n)*den(2)
      +den(2)*den(2)^(n+1)*S(R(-2-b),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-2-b),X(2),n)*b
      +den(2)*den(2)^(n+1)*S(R(-2-b),X(2),n)*n
      +den(2)*den(2)^(n+1)*S(R(-2-b),X(2),n)*n*b
      +2*den(2)*den(2)^(n+1)*S(R(2+b),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(2+b),X(2),n)*b
      +2*den(2)*den(2)^(n+1)*S(R(2+b),X(2),n)*n
      +den(2)*den(2)^(n+1)*S(R(2+b),X(2),n)*n*b
      -den(2)*den(2)^(n+1)*S(R(2,b),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(2,b),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(b),X(2),RU,RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(b),X(2),RU,RL,2,n)*n
      +den(2)*TT(R,X,RU(b),RL,1,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*b
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n*b;
* k=0, s=1, r=1, q_1=1 and p_1>1 (sommetjes equation 7.233) 
id GG(R,X,RU(a?{>1}),RL(1),0,n?) = -GG(R(1+a),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+a),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*a
      -GG(R(1+a),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+a),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n*a
      +GG(R(a),X(2),RU,RL(1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(1),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(a),X(2),RU,RL,2,n)*den(2)*den(2)^(n+1)
      -GG(R(a),X(2),RU,RL,2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL,1,n)*den(2)
      +GG(R,X,RU(1),RL,a,n)*den(2)
      -sum_(jjj,1,1+a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*a
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s=1, r=1, q_1=1 and p_1=1 (sommetjes equation 7.234)
id GG(R,X,RU(1),RL(1),0,n?) = GG(R(1),X(2),RU(1),RL,1,n)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1),RL,1,n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(1),1,n)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(1),1,n)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU,RL,2,n)*den(2)^(n+1)
      -GG(R(1),X(2),RU,RL,2,n)*den(2)^(n+1)*n
      -2*GG(R(2),X(2),RU,RL,1,n)*den(2)^(n+1)*(n+1)
      +GG(R,X,RU(1),RL,1,n);
* k=0, s=1, r=1, q_1=1 and p_1<-1 (sommetjes equation 7.235) 
id GG(R,X,RU(a?{<-1}),RL(1),0,n?) = abs_(a)*den(2)*den(2)^(n+1)*S(R(-2-abs_(a)),X(2),n)
      +abs_(a)*den(2)*den(2)^(n+1)*S(R(-2-abs_(a)),X(2),n)*n
      +abs_(a)*den(2)*den(2)^(n+1)*S(R(2+abs_(a)),X(2),n)
      +abs_(a)*den(2)*den(2)^(n+1)*S(R(2+abs_(a)),X(2),n)*n
      +GG(R(1),X(2),RU(a),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL,1,n)*den(2)
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(a)),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(a)),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),1),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),1),X(2,1),n)*n
      +2*den(2)*den(2)^(n+1)*S(R(2+abs_(a)),X(2),n)
      +2*den(2)*den(2)^(n+1)*S(R(2+abs_(a)),X(2),n)*n
      +den(2)*TT(R,X,RU(1),RL,abs_(a),n)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1=1 and p_1=-1 (sommetjes equation 7.236)
id GG(R,X,RU(-1),RL(1),0,n?) = GG(R(1),X(2),RU(-1),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL,1,n)*den(2)
      +den(2)^(n+1)*S(R(-3),X(2),n)
      +den(2)^(n+1)*S(R(-3),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(2,1),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(2,1),X(2,1),n)*n
      +3*den(2)*den(2)^(n+1)*S(R(3),X(2),n)
      +3*den(2)*den(2)^(n+1)*S(R(3),X(2),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL,2,n)*n
      +den(2)*TT(R,X,RU(1),RL,1,n);
* k=0, s=1, r=1, q_1<-1 and p_1>1 (sommetjes equation 7.237) 
id GG(R,X,RU(a?{>1}),RL(b?{<-1}),0,n?) = binom_(-1+a+abs_(b),-1+a)*den(2)*den(2)^(n+1)*S(R(-1-a-abs_(b)),X(2),n)
      +binom_(-1+a+abs_(b),-1+a)*den(2)*den(2)^(n+1)*S(R(-1-a-abs_(b)),X(2),n)*n
      +binom_(-1+a+abs_(b),-1+a)*den(2)*den(2)^(n+1)*S(R(1+a+abs_(b)),X(2),n)
      +binom_(-1+a+abs_(b),-1+a)*den(2)*den(2)^(n+1)*S(R(1+a+abs_(b)),X(2),n)*n
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*S(R(-1-a-abs_(b)),X(2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*S(R(-1-a-abs_(b)),X(2),n)*n
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*S(R(1+a+abs_(b)),X(2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*S(R(1+a+abs_(b)),X(2),n)*n
      +GG(R(a),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b),RL,a,n)*den(2)
      +den(2)*den(2)^(n+1)*S(R(1+a+abs_(b)),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(1+a+abs_(b)),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),a),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),a),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(-abs_(b)),X(2),RU,RL,1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(b)),X(2),RU,RL,1+a,n)*n
      +den(2)*TT(R,X,RU(a),RL,abs_(b),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1<-1 and p_1=1 (sommetjes equation 7.238)
id GG(R,X,RU(1),RL(b?{<-1}),0,n?) = abs_(b)*den(2)*den(2)^(n+1)*S(R(-2-abs_(b)),X(2),n)
      +abs_(b)*den(2)*den(2)^(n+1)*S(R(-2-abs_(b)),X(2),n)*n
      +abs_(b)*den(2)*den(2)^(n+1)*S(R(2+abs_(b)),X(2),n)
      +abs_(b)*den(2)*den(2)^(n+1)*S(R(2+abs_(b)),X(2),n)*n
      +GG(R(1),X(2),RU(b),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b),RL,1,n)*den(2)
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(b)),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(b)),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),1),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),1),X(2,1),n)*n
      +2*den(2)*den(2)^(n+1)*S(R(2+abs_(b)),X(2),n)
      +2*den(2)*den(2)^(n+1)*S(R(2+abs_(b)),X(2),n)*n
      +den(2)*TT(R,X,RU(1),RL,abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*abs_(b)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*abs_(b)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1<-1 and p_1<-1 (sommetjes equation 7.239) 
id GG(R,X,RU(a?{<-1}),RL(b?{<-1}),0,n?) = GG(R(-abs_(a)),X(2),RU,RL,1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(-abs_(a)),X(2),RU,RL,1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(-abs_(b)),X(2),RU,RL,1+abs_(a),n)*den(2)*den(2)^(n+1)
      +GG(R(-abs_(b)),X(2),RU,RL,1+abs_(a),n)*den(2)*den(2)^(n+1)*n
      +2*den(2)*den(2)^(n+1)*S(R(-1-abs_(a)-abs_(b)),X(2),n)
      +2*den(2)*den(2)^(n+1)*S(R(-1-abs_(a)-abs_(b)),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),b),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),b),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),a),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),a),X(2,1),n)*n
      +den(2)*TT(R,X,RU(a),RL,abs_(b),n)
      +den(2)*TT(R,X,RU(b),RL,abs_(a),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1<-1 and p_1=-1 (sommetjes equation 7.240)
id GG(R,X,RU(-1),RL(b?{<-1}),0,n?) = -abs_(b)*GG(R(-1-abs_(b)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)
      -abs_(b)*GG(R(-1-abs_(b)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(b)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(b)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(b)),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(b)),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),-1),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(b),-1),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*S(R(-(2+abs_(b))),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-(2+abs_(b))),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(2,b),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(2,b),X(2,1),n)*n
      +den(2)*TT(R,X,RU(b),RL,1,n)
      +den(2)*TT(R,X,RU(-1),RL,abs_(b),n)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n))*abs_(b)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n))*abs_(b)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1=-1 and p_1>1 (sommetjes equation 7.241) 
id GG(R,X,RU(a?{>1}),RL(-1),0,n?) = GG(R(a),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL,a,n)*den(2)
      +den(2)*den(2)^(n+1)*S(R(-2-a),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-2-a),X(2),n)*a
      +den(2)*den(2)^(n+1)*S(R(-2-a),X(2),n)*n
      +den(2)*den(2)^(n+1)*S(R(-2-a),X(2),n)*n*a
      +2*den(2)*den(2)^(n+1)*S(R(2+a),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(2+a),X(2),n)*a
      +2*den(2)*den(2)^(n+1)*S(R(2+a),X(2),n)*n
      +den(2)*den(2)^(n+1)*S(R(2+a),X(2),n)*n*a
      -den(2)*den(2)^(n+1)*S(R(2,a),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(2,a),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU,RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU,RL,2,n)*n
      +den(2)*TT(R,X,RU(a),RL,1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s=1, r=1, q_1=-1 and p_1=1 (sommetjes equation 7.242)
id GG(R,X,RU(1),RL(-1),0,n?) = GG(R(1),X(2),RU(-1),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL,1,n)*den(2)
      +2*den(2)*den(2)^(n+1)*S(R(-3),X(2),n)
      +2*den(2)*den(2)^(n+1)*S(R(-3),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(2,1),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(2,1),X(2,1),n)*n
      +3*den(2)*den(2)^(n+1)*S(R(3),X(2),n)
      +3*den(2)*den(2)^(n+1)*S(R(3),X(2),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL,2,n)*n
      +den(2)*TT(R,X,RU(1),RL,1,n);
* k=0, s=1, r=1, q_1=-1 and p_1<-1 (sommetjes equation 7.243) 
id GG(R,X,RU(a?{<-1}),RL(-1),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU,RL,1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(a)),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-2-abs_(a)),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),-1),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(1+abs_(a),-1),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*S(R(-(2+abs_(a))),X(2),n)
      +den(2)*den(2)^(n+1)*S(R(-(2+abs_(a))),X(2),n)*n
      -den(2)*den(2)^(n+1)*S(R(2,a),X(2,1),n)
      -den(2)*den(2)^(n+1)*S(R(2,a),X(2,1),n)*n
      +den(2)*TT(R,X,RU(a),RL,1,n)
      +den(2)*TT(R,X,RU(-1),RL,abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r=1, q_1=-1 and p_1=-1 (sommetjes equation 7.244)
id GG(R,X,RU(-1),RL(-1),0,n?) = -2*GG(R(-2),X(2),RU,RL,1,n)*den(2)^(n+1)*(n+1)
      -den(2)^(n+1)*S(R(2,-1),X(2,1),n)
      -den(2)^(n+1)*S(R(2,-1),X(2,1),n)*n
      +den(2)^(n+1)*S(R(-3),X(2),n)
      +den(2)^(n+1)*S(R(-3),X(2),n)*n
      +2*den(2)*TT(R,X,RU(-1),RL,1,n);
**********
* k=0, s=1, r>1, q_1>1 and p_1>1 (sommetjes equation 7.245) 
id GG(R,X,RU(a?{>1}),RL(b?{>1},c?,?d),0,n?) = GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL(c,?d),b,n)*den(2)
      +GG(R,X,RU(b,c,?d),RL,a,n)*den(2)
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(1-jjj+b+a),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(1-jjj+b+a),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(1-jjj+b+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(1-jjj+b+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(1-jjj+b+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(1-jjj+b+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(1-jjj+b+a),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(1-jjj+b+a),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1>1 and p_1=1 (sommetjes equation 7.246)
id GG(R,X,RU(1),RL(b?{>1},c?,?d),0,n?) = -GG(R(1+b),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+b),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)*b
      -GG(R(1+b),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+b),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n*b
      +GG(R(b),X(2),RU(c,?d),RL(1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU(c,?d),RL(1),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(b),X(2),RU(c,?d),RL,2,n)*den(2)*den(2)^(n+1)
      -GG(R(b),X(2),RU(c,?d),RL,2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b,c,?d),RL,1,n)*den(2)
      +GG(R,X,RU(1),RL(c,?d),b,n)*den(2)
      -sum_(jjj,1,1+b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*b
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n*b;
* k=0, s=1, r>1, q_1>1, p_1<-1 and q_2>=0 (sommetjes equation 7.247)
id GG(R,X,RU(a?{<-1}),RL(b?{>1},c?{>=0},?d),0,n?) = -binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+c+b+abs_(a),?d),X(2),n)
      -binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+c+b+abs_(a),?d),X(2),n)*n
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)*n
      -binom_(-1+b+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(-b-abs_(a)),X(2),RU,RL(?d),1+c,n)
      -binom_(-1+b+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(-b-abs_(a)),X(2),RU,RL(?d),1+c,n)*n
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+c+b+abs_(a),?d),X(2),n)
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+c+b+abs_(a),?d),X(2),n)*n
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)*n
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*TT(R(-b-abs_(a)),X(2),RU,RL(?d),1+c,n)
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*TT(R(-b-abs_(a)),X(2),RU,RL(?d),1+c,n)*n
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL(c,?d),b,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU,RL(c,?d),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU,RL(c,?d),1+b,n)*n
      +den(2)*TT(R,X,RU(b,c,?d),RL,abs_(a),n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1>1, p_1<-1 and q_2<0 (sommetjes equation 7.248)
id GG(R,X,RU(a?{<-1}),RL(b?{>1},c?{<0},?d),0,n?) = -binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-b-abs_(a)-abs_(c),?d),X(2),n)
      -binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-b-abs_(a)-abs_(c),?d),X(2),n)*n
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)*n
      -binom_(-1+b+abs_(a),abs_(a))*GG(R(-b-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -binom_(-1+b+abs_(a),abs_(a))*GG(R(-b-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+b+abs_(a),b)*GG(R(-b-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -binom_(-1+b+abs_(a),b)*GG(R(-b-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-b-abs_(a)-abs_(c),?d),X(2),n)
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-b-abs_(a)-abs_(c),?d),X(2),n)*n
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)*n
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL(c,?d),b,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU,RL(c,?d),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU,RL(c,?d),1+b,n)*n
      +den(2)*TT(R,X,RU(b,c,?d),RL,abs_(a),n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1>1, p_1=-1 and q_2>=0 (sommetjes equation 7.249)
id GG(R,X,RU(-1),RL(b?{>1},c?{>=0},?d),0,n?) = GG(R(b),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(c,?d),b,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+b,?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+b,?d),X(2),n)*b
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+b,?d),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+b,?d),X(2),n)*n*b
      +2*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*b
      +2*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*n*b
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-b),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-b),X(2),RU,RL(?d),1+c,n)*b
      -den(2)*den(2)^(n+1)*TT(R(-1-b),X(2),RU,RL(?d),1+c,n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-b),X(2),RU,RL(?d),1+c,n)*n*b
      -den(2)*den(2)^(n+1)*TT(R(b),X(2),RU(c,?d),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(b),X(2),RU(c,?d),RL,2,n)*n
      +den(2)*TT(R,X,RU(b,c,?d),RL,1,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*b
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n*b;
* k=0, s=1, r>1, q_1>1, p_1=-1 and q_2<0 (sommetjes equation 7.250)
id GG(R,X,RU(-1),RL(b?{>1},c?{<0},?d),0,n?) = -GG(R(-1-b),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-b),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*b
      -GG(R(-1-b),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-b),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n*b
      +GG(R(b),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(b),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(c,?d),b,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-b-abs_(c),?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-b-abs_(c),?d),X(2),n)*b
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-b-abs_(c),?d),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-b-abs_(c),?d),X(2),n)*n*b
      +2*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*b
      +2*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*n*b
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(b),X(2),RU(c,?d),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(b),X(2),RU(c,?d),RL,2,n)*n
      +den(2)*TT(R,X,RU(b,c,?d),RL,1,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*b
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n*b;
* k=0, s=1, r>1, q_1=1 and p_1>1 (sommetjes equation 7.251)
id GG(R,X,RU(a?{>1}),RL(1,c?,?d),0,n?) = -GG(R(1+a),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+a),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)*a
      -GG(R(1+a),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+a),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n*a
      -GG(R(a),X(2),RU,RL(c,?d),2,n)*den(2)*den(2)^(n+1)
      -GG(R(a),X(2),RU,RL(c,?d),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(a),X(2),RU,RL(1,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(1,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU(c,?d),RL,1+a,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU(c,?d),RL,1+a,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL(c,?d),1,n)*den(2)
      +GG(R,X,RU(1,c,?d),RL,a,n)*den(2)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s=1, r>1, q_1=1 and p_1=1 (sommetjes equation 7.252)
id GG(R,X,RU(1),RL(1,c?,?d),0,n?) = GG(R(1),X(2),RU(c,?d),RL(1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(c,?d),RL(1),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU(c,?d),RL,2,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU(c,?d),RL,2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1),RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1),RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU,RL(c,?d),2,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU,RL(c,?d),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(1,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(1,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(c,?d),RL,1,n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(c,?d),RL,1,n)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU,RL(c,?d),1,n)*den(2)^(n+1)
      -GG(R(2),X(2),RU,RL(c,?d),1,n)*den(2)^(n+1)*n
      +GG(R,X,RU(1),RL(c,?d),1,n)*den(2)
      +GG(R,X,RU(1,c,?d),RL,1,n)*den(2);
* k=0, s=1, r>1, q_1=1, p_1<-1 and q_2>=0 (sommetjes equation 7.253)
id GG(R,X,RU(a?{<-1}),RL(1,c?{>=0},?d),0,n?) = -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+abs_(a),?d),X(2),n)
      -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+abs_(a),?d),X(2),n)*n
      +(abs_(a)+2)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+abs_(a),c,?d),X(2,1),n)
      +(abs_(a)+2)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+abs_(a),c,?d),X(2,1),n)*n
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU,RL(?d),1+c,n)
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU,RL(?d),1+c,n)*n
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL(c,?d),1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),1,c,?d),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+abs_(a),?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+c+abs_(a),?d),X(2),n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU,RL(?d),1+c,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,1+abs_(a),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(1,c,?d),RL,abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1=1, p_1<-1 and q_2<0 (sommetjes equation 7.254)
id GG(R,X,RU(a?{<-1}),RL(1,c?{<0},?d),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a)-abs_(c),?d),X(2),n)
      -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a)-abs_(c),?d),X(2),n)*n
      +(abs_(a)+2)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+abs_(a),c,?d),X(2,1),n)
      +(abs_(a)+2)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+abs_(a),c,?d),X(2,1),n)*n
      -GG(R(-1-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a),RL(c,?d),1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a)-abs_(c),?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a)-abs_(c),?d),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),1,c,?d),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,1+abs_(a),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(1,c,?d),RL,abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1=1, p_1=-1 and q_2>=0 (sommetjes equation 7.255)
id GG(R,X,RU(-1),RL(1,c?{>=0},?d),0,n?) = GG(R(1),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1),RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(c,?d),1,n)*den(2)
      -den(2)^(n+1)*TT(R(-2),X(2),RU,RL(?d),1+c,n)
      -den(2)^(n+1)*TT(R(-2),X(2),RU,RL(?d),1+c,n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,1,c,?d),X(2,1,1),n)*n
      +3*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(3,c,?d),X(2,1),n)
      +3*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(3,c,?d),X(2,1),n)*n
      -(n+1)*den(2)^(n+1)*g(nargs_(?d))*S(R(c+3,?d),X(2),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,2,n)*n
      +den(2)*TT(R,X,RU(1,c,?d),RL,1,n);
* k=0, s=1, r>1, q_1=1, p_1=-1 and q_2<0 (sommetjes equation 7.256)
id GG(R,X,RU(-1),RL(1,c?{<0},?d),0,n?) = -GG(R(-2),X(2),RU,RL(?d),1+abs_(c),n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU,RL(?d),1+abs_(c),n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1),RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(c,?d),1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,1,c,?d),X(2,1,1),n)*n
      +3*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(3,c,?d),X(2,1),n)
      +3*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(3,c,?d),X(2,1),n)*n
      -(n+1)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(abs_(c)+3),?d),X(2),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(c,?d),RL,2,n)*n
      +den(2)*TT(R,X,RU(1,c,?d),RL,1,n);
* k=0, s=1, r>1, q_1<-1, p_1>1 and q_2>=0 (sommetjes equation 7.257)
id GG(R,X,RU(a?{>1}),RL(b?{<-1},c?{>=0},?d),0,n?) = -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-c-a-abs_(b),?d),X(2),n)
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-c-a-abs_(b),?d),X(2),n)*n
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-a-abs_(b),c,?d),X(2,1),n)
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-a-abs_(b),c,?d),X(2,1),n)*n
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*TT(R(a+abs_(b)),X(2),RU,RL(?d),1+c,n)
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*TT(R(a+abs_(b)),X(2),RU,RL(?d),1+c,n)*n
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(1+c+a+abs_(b)),?d),X(2),n)
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(1+c+a+abs_(b)),?d),X(2),n)*n
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(1+a+abs_(b)),c,?d),X(2,1),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(1+a+abs_(b)),c,?d),X(2,1),n)*n
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(b)),X(2),RU,RL(?d),1+c,n)
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(b)),X(2),RU,RL(?d),1+c,n)*n
      +GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b,c,?d),RL,a,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(b)),X(2),RU(c,?d),RL,1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(b)),X(2),RU(c,?d),RL,1+a,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(a),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(a),RL(?d),1+c,n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),abs_(b),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1<-1, p_1>1 and q_2<0 (sommetjes equation 7.258)
id GG(R,X,RU(a?{>1}),RL(b?{<-1},c?{<0},?d),0,n?) = -binom_(-1+a+abs_(b),abs_(b))*GG(R(a+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(b),abs_(b))*GG(R(a+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-a-abs_(b),c,?d),X(2,1),n)
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-a-abs_(b),c,?d),X(2,1),n)*n
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+a+abs_(b)+abs_(c),?d),X(2),n)
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+a+abs_(b)+abs_(c),?d),X(2),n)*n
      -binom_(-1+a+abs_(b),a)*GG(R(a+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(b),a)*GG(R(a+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(-1-a-abs_(b)-abs_(c)),?d),X(2),n)
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(-1-a-abs_(b)-abs_(c)),?d),X(2),n)*n
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(1+a+abs_(b)),c,?d),X(2,1),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(1+a+abs_(b)),c,?d),X(2,1),n)*n
      +GG(R(abs_(b)),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(b)),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b,c,?d),RL,a,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(b)),X(2),RU(c,?d),RL,1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(b)),X(2),RU(c,?d),RL,1+a,n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),abs_(b),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1<-1, p_1=1 and q_2>=0 (sommetjes equation 7.259)
id GG(R,X,RU(1),RL(b?{<-1},c?{>=0},?d),0,n?) = -abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+c+abs_(b)),?d),X(2),n)
      -abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+c+abs_(b)),?d),X(2),n)*n
      +abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      +abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)*n
      -abs_(b)*den(2)*den(2)^(n+1)*TT(R(1+abs_(b)),X(2),RU,RL(?d),1+c,n)
      -abs_(b)*den(2)*den(2)^(n+1)*TT(R(1+abs_(b)),X(2),RU,RL(?d),1+c,n)*n
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b,c,?d),RL,1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-c-abs_(b),?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-c-abs_(b),?d),X(2),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(b),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(b),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(b)),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(b)),X(2),RU,RL(?d),1+c,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(1),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(1),RL(?d),1+c,n)*n
      +den(2)*TT(R,X,RU(1),RL(c,?d),abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1<-1, p_1=1 and q_2<0 (sommetjes equation 7.260)
id GG(R,X,RU(1),RL(b?{<-1},c?{<0},?d),0,n?) = -abs_(b)*GG(R(1+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -abs_(b)*GG(R(1+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(-2-abs_(b)-abs_(c)),?d),X(2),n)
      -abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(-2-abs_(b)-abs_(c)),?d),X(2),n)*n
      +abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      +abs_(b)*den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)*n
      -GG(R(1+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -GG(R(1+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(b)),X(2),RU(1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(b)),X(2),RU(1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(b,c,?d),RL,1,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(b),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(b),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+abs_(b)+abs_(c),?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+abs_(b)+abs_(c),?d),X(2),n)*n
      +den(2)*TT(R,X,RU(1),RL(c,?d),abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1<-1, p_1<-1 and q_2>=0 (sommetjes equation 7.261)
id GG(R,X,RU(a?{<-1}),RL(b?{<-1},c?{>=0},?d),0,n?) = GG(R(-abs_(a)),X(2),RU,RL(c,?d),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(-abs_(a)),X(2),RU,RL(c,?d),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-abs_(a)-abs_(b),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-abs_(a)-abs_(b),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(b)),X(2),RU(c,?d),RL,1+abs_(a),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(b)),X(2),RU(c,?d),RL,1+abs_(a),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(a),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(a),RL(?d),1+c,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a),RL(c,?d),abs_(b),n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a),RL(c,?d),abs_(b),n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,c,?d),RL,abs_(a),n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,c,?d),RL,abs_(a),n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),abs_(b),n)
      +den(2)*TT(R,X,RU(b,c,?d),RL,abs_(a),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,-1+abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,-1+abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,-1+abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,-1+abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1<-1, p_1<-1 and q_2<0 (sommetjes equation 7.262)
id GG(R,X,RU(a?{<-1}),RL(b?{<-1},c?{<0},?d),0,n?) = GG(R(-abs_(a)),X(2),RU,RL(c,?d),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(-abs_(a)),X(2),RU,RL(c,?d),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(b)),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(b)),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-abs_(a)-abs_(b),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-1-abs_(a)-abs_(b),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(b)),X(2),RU(c,?d),RL,1+abs_(a),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(b)),X(2),RU(c,?d),RL,1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),abs_(b),n)
      +den(2)*TT(R,X,RU(b,c,?d),RL,abs_(a),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1<-1, p_1=-1 and q_2>=0 (sommetjes equation 7.263)
id GG(R,X,RU(-1),RL(b?{<-1},c?{>=0},?d),0,n?) = -abs_(b)*GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      -abs_(b)*GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(-1),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(b)),X(2),RU(-1),RL(?d),1+c,n)*n
      +den(2)*TT(R,X,RU(b,c,?d),RL,1,n)
      +den(2)*TT(R,X,RU(-1),RL(c,?d),abs_(b),n)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1<-1, p_1=-1 and q_2<0 (sommetjes equation 7.264)
id GG(R,X,RU(-1),RL(b?{<-1},c?{<0},?d),0,n?) = -abs_(b)*GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      -abs_(b)*GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(b)),X(2),RU(-1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(b)),X(2),RU(-1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)*n
      +den(2)*TT(R,X,RU(b,c,?d),RL,1,n)
      +den(2)*TT(R,X,RU(-1),RL(c,?d),abs_(b),n)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1=-1, p_1>1 and q_2>=0 (sommetjes equation 7.265)
id GG(R,X,RU(a?{>1}),RL(-1,c?{>=0},?d),0,n?) = GG(R(a),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,c,?d),RL,a,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-c-a,?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-c-a,?d),X(2),n)*a
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-c-a,?d),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-c-a,?d),X(2),n)*n*a
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*a
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU,RL(?d),1+c,n)*a
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU,RL(?d),1+c,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU,RL(?d),1+c,n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU,RL(c,?d),2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU,RL(c,?d),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a),RL(?d),1+c,n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s=1, r>1, q_1=-1, p_1>1 and q_2<0 (sommetjes equation 7.266)
id GG(R,X,RU(a?{>1}),RL(-1,c?{<0},?d),0,n?) = -GG(R(1+a),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      -GG(R(1+a),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*a
      -GG(R(1+a),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+a),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n*a
      +GG(R(a),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,c,?d),RL,a,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*a
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*n*a
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+a+abs_(c),?d),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+a+abs_(c),?d),X(2),n)*a
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+a+abs_(c),?d),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2+a+abs_(c),?d),X(2),n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU,RL(c,?d),2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU,RL(c,?d),2,n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s=1, r>1, q_1=-1, p_1=1 and q_2>=0 (sommetjes equation 7.267)
id GG(R,X,RU(1),RL(-1,c?{>=0},?d),0,n?) = GG(R(1),X(2),RU(-1,c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,c,?d),RL,1,n)*den(2)
      -den(2)^(n+1)*g(nargs_(?d))*S(R(-3-c,?d),X(2),n)
      -den(2)^(n+1)*g(nargs_(?d))*S(R(-3-c,?d),X(2),n)*n
      +den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      +den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)*n
      -den(2)^(n+1)*TT(R(2),X(2),RU,RL(?d),1+c,n)
      -den(2)^(n+1)*TT(R(2),X(2),RU,RL(?d),1+c,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1),RL(?d),1+c,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(c,?d),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(c,?d),2,n)*n
      +den(2)*TT(R,X,RU(1),RL(c,?d),1,n);
* k=0, s=1, r>1, q_1=-1, p_1=1 and q_2<0 (sommetjes equation 7.268)
id GG(R,X,RU(1),RL(-1,c?{<0},?d),0,n?) = GG(R(1),X(2),RU(-1,c,?d),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,c,?d),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU,RL(?d),1+abs_(c),n)*den(2)^(n+1)
      -GG(R(2),X(2),RU,RL(?d),1+abs_(c),n)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,c,?d),RL,1,n)*den(2)
      -den(2)^(n+1)*g(nargs_(?d))*S(R(3+abs_(c),?d),X(2),n)
      -den(2)^(n+1)*g(nargs_(?d))*S(R(3+abs_(c),?d),X(2),n)*n
      +den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      +den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(c,?d),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(c,?d),2,n)*n
      +den(2)*TT(R,X,RU(1),RL(c,?d),1,n);
* k=0, s=1, r>1, q_1=-1, p_1<-1 and q_2>=0 (sommetjes equation 7.269)
id GG(R,X,RU(a?{<-1}),RL(-1,c?{>=0},?d),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),-1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),-1,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a),RL(?d),1+c,n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),1,n)
      +den(2)*TT(R,X,RU(-1,c,?d),RL,abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1=-1, p_1<-1 and q_2<0 (sommetjes equation 7.270)
id GG(R,X,RU(a?{<-1}),RL(-1,c?{<0},?d),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a),c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-2-abs_(a),c,?d),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),-1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(1+abs_(a),-1,c,?d),X(2,1,1),n)*n
      +den(2)*TT(R,X,RU(a),RL(c,?d),1,n)
      +den(2)*TT(R,X,RU(-1,c,?d),RL,abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s=1, r>1, q_1=-1, p_1=-1 and q_2>=0 (sommetjes equation 7.271)
id GG(R,X,RU(-1),RL(-1,c?{>=0},?d),0,n?) = -GG(R(-2),X(2),RU,RL(c,?d),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU,RL(c,?d),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(c,?d),RL,1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(c,?d),RL,1,n)*den(2)^(n+1)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,-1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,-1,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1),RL(?d),1+c,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1),RL(?d),1+c,n)*n
      +den(2)*TT(R,X,RU(-1),RL(c,?d),1,n)
      +den(2)*TT(R,X,RU(-1,c,?d),RL,1,n);
* k=0, s=1, r>1, q_1=-1, p_1=-1 and q_2<0 (sommetjes equation 7.272)
id GG(R,X,RU(-1),RL(-1,c?{<0},?d),0,n?) = -GG(R(-2),X(2),RU,RL(c,?d),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU,RL(c,?d),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(c,?d),RL,1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(c,?d),RL,1,n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n+1)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,-1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(2,-1,c,?d),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)*n
      +den(2)*TT(R,X,RU(-1),RL(c,?d),1,n)
      +den(2)*TT(R,X,RU(-1,c,?d),RL,1,n);
**********
* k=0, s>1, r=1, q_1>1 and p_1>1 (sommetjes equation 7.273) 
id GG(R,X,RU(a?{>1},b?,?c),RL(d?{>1}),0,n?) = GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d),RL(b,?c),a,n)*den(2)
      +GG(R,X,RU(a,b,?c),RL,d,n)*den(2)
      -sum_(jjj,1,1+d,binom_(-jjj+d+a,-1+a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+d,binom_(-jjj+d+a,-1+a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+a,binom_(-jjj+d+a,-1+d)*GG(R(1-jjj+d+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+a,binom_(-jjj+d+a,-1+d)*GG(R(1-jjj+d+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,binom_(-jjj+d+a,d)*GG(R(1-jjj+d+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,binom_(-jjj+d+a,d)*GG(R(1-jjj+d+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,d,binom_(-jjj+d+a,a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,d,binom_(-jjj+d+a,a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1>1 and p_1=1 (sommetjes equation 7.274)
id GG(R,X,RU(1,b?,?c),RL(d?{>1}),0,n?) = -GG(R(1+d),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+d),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)*d
      -GG(R(1+d),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+d),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n*d
      -GG(R(d),X(2),RU,RL(b,?c),2,n)*den(2)*den(2)^(n+1)
      -GG(R(d),X(2),RU,RL(b,?c),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(d),X(2),RU,RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU,RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU(b,?c),RL,1+d,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU(b,?c),RL,1+d,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d),RL(b,?c),1,n)*den(2)
      +GG(R,X,RU(1,b,?c),RL,d,n)*den(2)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*d
      -2*sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r=1, q_1>1, p_1<-1 and p_2>=0 (sommetjes equation 7.275)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{>1}),0,n?) = -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-d-b-abs_(a),?c),X(2),n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-d-b-abs_(a),?c),X(2),n)*n
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-d-abs_(a),b,?c),X(2,1),n)
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-d-abs_(a),b,?c),X(2,1),n)*n
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU,RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU,RL(?c),1+b,n)*n
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(1+d+b+abs_(a)),?c),X(2),n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(1+d+b+abs_(a)),?c),X(2),n)*n
      +binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(1+d+abs_(a)),b,?c),X(2,1),n)
      +binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(1+d+abs_(a)),b,?c),X(2,1),n)*n
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU,RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU,RL(?c),1+b,n)*n
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL,d,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL,1+d,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL,1+d,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),abs_(a),n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1>1, p_1<-1 and p_2<0 (sommetjes equation 7.276)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{>1}),0,n?) = -binom_(-1+d+abs_(a),abs_(a))*GG(R(d+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(d+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-d-abs_(a),b,?c),X(2,1),n)
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-d-abs_(a),b,?c),X(2,1),n)*n
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+d+abs_(a)+abs_(b),?c),X(2),n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+d+abs_(a)+abs_(b),?c),X(2),n)*n
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(-1-d-abs_(a)-abs_(b)),?c),X(2),n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(-1-d-abs_(a)-abs_(b)),?c),X(2),n)*n
      +binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(1+d+abs_(a)),b,?c),X(2,1),n)
      +binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(1+d+abs_(a)),b,?c),X(2,1),n)*n
      +GG(R(abs_(a)),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL,d,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL,1+d,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL,1+d,n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),abs_(a),n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1>1, p_1=-1 and p_2>=0 (sommetjes equation 7.277)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{>1}),0,n?) = GG(R(d),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL,d,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)*d
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)*n*d
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d-b,?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d-b,?c),X(2),n)*d
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d-b,?c),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d-b,?c),X(2),n)*n*d
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU,RL(?c),1+b,n)*d
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU,RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU,RL(?c),1+b,n)*n*d
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU,RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU,RL(b,?c),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),1,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*d
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r=1, q_1>1, p_1=-1 and p_2<0 (sommetjes equation 7.278)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{>1}),0,n?) = -GG(R(1+d),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(1+d),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*d
      -GG(R(1+d),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+d),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n*d
      +GG(R(d),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL,d,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)*d
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-d,b,?c),X(2,1),n)*n*d
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+d+abs_(b),?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+d+abs_(b),?c),X(2),n)*d
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+d+abs_(b),?c),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+d+abs_(b),?c),X(2),n)*n*d
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU,RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU,RL(b,?c),2,n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),1,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*d
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r=1, q_1=1 and p_1>1 (sommetjes equation 7.279)
id GG(R,X,RU(a?{>1},b?,?c),RL(1),0,n?) = -GG(R(1+a),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+a),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)*a
      -GG(R(1+a),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+a),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n*a
      +GG(R(a),X(2),RU(b,?c),RL(1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(1),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(a),X(2),RU(b,?c),RL,2,n)*den(2)*den(2)^(n+1)
      -GG(R(a),X(2),RU(b,?c),RL,2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL,1,n)*den(2)
      +GG(R,X,RU(1),RL(b,?c),a,n)*den(2)
      -sum_(jjj,1,1+a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r=1, q_1=1 and p_1=1 (sommetjes equation 7.280)
id GG(R,X,RU(1,b?,?c),RL(1),0,n?) = GG(R(1),X(2),RU(b,?c),RL(1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(1),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU(b,?c),RL,2,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU(b,?c),RL,2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU,RL(b,?c),2,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU,RL(b,?c),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(b,?c),RL,1,n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(b,?c),RL,1,n)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU,RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(2),X(2),RU,RL(b,?c),1,n)*den(2)^(n+1)*n
      +GG(R,X,RU(1),RL(b,?c),1,n)*den(2)
      +GG(R,X,RU(1,b,?c),RL,1,n)*den(2);
* k=0, s>1, r=1, q_1=1, p_1<-1 and p_2>=0 (sommetjes equation 7.281)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(1),0,n?) = -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+b+abs_(a)),?c),X(2),n)
      -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+b+abs_(a)),?c),X(2),n)*n
      +abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      +abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)*n
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU,RL(?c),1+b,n)
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU,RL(?c),1+b,n)*n
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL,1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-b-abs_(a),?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-b-abs_(a),?c),X(2),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(a),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(a),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU,RL(?c),1+b,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(1),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(1),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(1),RL(b,?c),abs_(a),n)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1=1, p_1<-1 and p_2<0 (sommetjes equation 7.282)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(1),0,n?) = -abs_(a)*GG(R(1+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(1+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(-2-abs_(a)-abs_(b)),?c),X(2),n)
      -abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(-2-abs_(a)-abs_(b)),?c),X(2),n)*n
      +abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      +abs_(a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)*n
      -GG(R(1+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(1+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(a)),X(2),RU(1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL,1,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(a),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(a),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+abs_(a)+abs_(b),?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+abs_(a)+abs_(b),?c),X(2),n)*n
      +den(2)*TT(R,X,RU(1),RL(b,?c),abs_(a),n)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1=1, p_1=-1 and p_2>=0 (sommetjes equation 7.283)
id GG(R,X,RU(-1,b?{>=0},?c),RL(1),0,n?) = GG(R(1),X(2),RU(-1,b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL,1,n)*den(2)
      -den(2)^(n+1)*g(nargs_(?c))*S(R(-3-b,?c),X(2),n)
      -den(2)^(n+1)*g(nargs_(?c))*S(R(-3-b,?c),X(2),n)*n
      +den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      +den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)*n
      -den(2)^(n+1)*TT(R(2),X(2),RU,RL(?c),1+b,n)
      -den(2)^(n+1)*TT(R(2),X(2),RU,RL(?c),1+b,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),2,n)*n
      +den(2)*TT(R,X,RU(1),RL(b,?c),1,n);
* k=0, s>1, r=1, q_1=1, p_1=-1 and p_2<0 (sommetjes equation 7.284)
id GG(R,X,RU(-1,b?{<0},?c),RL(1),0,n?) = GG(R(1),X(2),RU(-1,b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU,RL(?c),1+abs_(b),n)*den(2)^(n+1)
      -GG(R(2),X(2),RU,RL(?c),1+abs_(b),n)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL,1,n)*den(2)
      -den(2)^(n+1)*g(nargs_(?c))*S(R(3+abs_(b),?c),X(2),n)
      -den(2)^(n+1)*g(nargs_(?c))*S(R(3+abs_(b),?c),X(2),n)*n
      +den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      +den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),2,n)*n
      +den(2)*TT(R,X,RU(1),RL(b,?c),1,n);
* k=0, s>1, r=1, q_1<-1, p_1>1 and p_2>=0 (sommetjes equation 7.285)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(d?{<-1}),0,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+b+a+abs_(d),?c),X(2),n)
      -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+b+a+abs_(d),?c),X(2),n)*n
      +binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      +binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)*n
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU,RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU,RL(?c),1+b,n)*n
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+b+a+abs_(d),?c),X(2),n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+b+a+abs_(d),?c),X(2),n)*n
      +binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      +binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)*n
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU,RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU,RL(?c),1+b,n)*n
      +GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d),RL(b,?c),a,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU,RL(b,?c),1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU,RL(b,?c),1+a,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL,abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1<-1, p_1>1 and p_2<0 (sommetjes equation 7.286)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(d?{<-1}),0,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-a-abs_(b)-abs_(d),?c),X(2),n)
      -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-a-abs_(b)-abs_(d),?c),X(2),n)*n
      +binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      +binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)*n
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-a-abs_(b)-abs_(d),?c),X(2),n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-a-abs_(b)-abs_(d),?c),X(2),n)*n
      +binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      +binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)*n
      +GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d),RL(b,?c),a,n)*den(2)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU,RL(b,?c),1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU,RL(b,?c),1+a,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL,abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1<-1, p_1=1 and p_2>=0 (sommetjes equation 7.287)
id GG(R,X,RU(1,b?{>=0},?c),RL(d?{<-1}),0,n?) = -abs_(d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+abs_(d),?c),X(2),n)
      -abs_(d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+abs_(d),?c),X(2),n)*n
      +(abs_(d)+2)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+abs_(d),b,?c),X(2,1),n)
      +(abs_(d)+2)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+abs_(d),b,?c),X(2,1),n)*n
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU,RL(?c),1+b,n)
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU,RL(?c),1+b,n)*n
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),1,b,?c),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+abs_(d),?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+abs_(d),?c),X(2),n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU,RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,1+abs_(d),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,1+abs_(d),n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL,abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1<-1, p_1=1 and p_2<0 (sommetjes equation 7.288)
id GG(R,X,RU(1,b?{<0},?c),RL(d?{<-1}),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -abs_(d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(b)-abs_(d),?c),X(2),n)
      -abs_(d)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(b)-abs_(d),?c),X(2),n)*n
      +(abs_(d)+2)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+abs_(d),b,?c),X(2,1),n)
      +(abs_(d)+2)*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+abs_(d),b,?c),X(2,1),n)*n
      -GG(R(-1-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(b)-abs_(d),?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(b)-abs_(d),?c),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),1,b,?c),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,1+abs_(d),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,1+abs_(d),n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL,abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1<-1, p_1<-1 and p_2>=0 (sommetjes equation 7.289)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{<-1}),0,n?) = GG(R(-abs_(d)),X(2),RU,RL(b,?c),1+abs_(a),n)*den(2)*den(2)^(n+1)
      +GG(R(-abs_(d)),X(2),RU,RL(b,?c),1+abs_(a),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-abs_(a)-abs_(d),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-abs_(a)-abs_(d),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL,1+abs_(d),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL,1+abs_(d),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),abs_(a),n)
      +den(2)*TT(R,X,RU(a,b,?c),RL,abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1<-1, p_1<-1 and p_2<0 (sommetjes equation 7.290)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{<-1}),0,n?) = GG(R(abs_(a)),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(-abs_(d)),X(2),RU,RL(b,?c),1+abs_(a),n)*den(2)*den(2)^(n+1)
      +GG(R(-abs_(d)),X(2),RU,RL(b,?c),1+abs_(a),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-abs_(a)-abs_(d),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-1-abs_(a)-abs_(d),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL,1+abs_(d),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL,1+abs_(d),n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),abs_(a),n)
      +den(2)*TT(R,X,RU(a,b,?c),RL,abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1<-1, p_1=-1 and p_2>=0 (sommetjes equation 7.291)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{<-1}),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(d),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(d),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),-1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),-1,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL,abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1<-1, p_1=-1 and p_2<0 (sommetjes equation 7.292)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{<-1}),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(d),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-abs_(d),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),-1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(1+abs_(d),-1,b,?c),X(2,1,1),n)*n
      +den(2)*TT(R,X,RU(d),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL,abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1=-1, p_1>1 and p_2>=0 (sommetjes equation 7.293)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(-1),0,n?) = GG(R(a),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(b,?c),a,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+a,?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+a,?c),X(2),n)*a
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+a,?c),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+b+a,?c),X(2),n)*n*a
      +2*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*a
      +2*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*n*a
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU,RL(?c),1+b,n)*a
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU,RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU,RL(?c),1+b,n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL,2,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL,1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r=1, q_1=-1, p_1>1 and p_2<0 (sommetjes equation 7.294)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(-1),0,n?) = -GG(R(-1-a),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-a),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*a
      -GG(R(-1-a),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-a),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n*a
      +GG(R(a),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(b,?c),a,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-a-abs_(b),?c),X(2),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-a-abs_(b),?c),X(2),n)*a
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-a-abs_(b),?c),X(2),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-2-a-abs_(b),?c),X(2),n)*n*a
      +2*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*a
      +2*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*n*a
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)*n
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL,2,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL,1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r=1, q_1=-1, p_1=1 and p_2>=0 (sommetjes equation 7.295)
id GG(R,X,RU(1,b?{>=0},?c),RL(-1),0,n?) = GG(R(1),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(b,?c),1,n)*den(2)
      -den(2)^(n+1)*TT(R(-2),X(2),RU,RL(?c),1+b,n)
      -den(2)^(n+1)*TT(R(-2),X(2),RU,RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,1,b,?c),X(2,1,1),n)*n
      +3*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(3,b,?c),X(2,1),n)
      +3*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(3,b,?c),X(2,1),n)*n
      -(n+1)*den(2)^(n+1)*g(nargs_(?c))*S(R(b+3,?c),X(2),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,2,n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL,1,n);
* k=0, s>1, r=1, q_1=-1, p_1=1 and p_2<0 (sommetjes equation 7.296)
id GG(R,X,RU(1,b?{<0},?c),RL(-1),0,n?) = -GG(R(-2),X(2),RU,RL(?c),1+abs_(b),n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU,RL(?c),1+abs_(b),n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,1,b,?c),X(2,1,1),n)*n
      +3*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(3,b,?c),X(2,1),n)
      +3*den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(3,b,?c),X(2,1),n)*n
      -(n+1)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(abs_(b)+3),?c),X(2),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL,2,n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL,1,n);
* k=0, s>1, r=1, q_1=-1, p_1<-1 and p_2>=0 (sommetjes equation 7.297)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(-1),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(-1),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(-1),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL,1,n)
      +den(2)*TT(R,X,RU(-1),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1=-1, p_1<-1 and p_2<0 (sommetjes equation 7.298)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(-1),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(a)),X(2),RU(-1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(-1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL,1,n)
      +den(2)*TT(R,X,RU(-1),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r=1, q_1=-1, p_1=-1 and p_2>=0 (sommetjes equation 7.299)
id GG(R,X,RU(-1,b?{>=0},?c),RL(-1),0,n?) = -GG(R(-2),X(2),RU,RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU,RL(b,?c),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(b,?c),RL,1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL,1,n)*den(2)^(n+1)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,-1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,-1,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(-1),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL,1,n);
* k=0, s>1, r=1, q_1=-1, p_1=-1 and p_2<0 (sommetjes equation 7.300)
id GG(R,X,RU(-1,b?{<0},?c),RL(-1),0,n?) = -GG(R(-2),X(2),RU,RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU,RL(b,?c),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(b,?c),RL,1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL,1,n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,-1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(2,-1,b,?c),X(2,1,1),n)*n
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      +den(2)*den(2)^(n+1)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)*n
      +den(2)*TT(R,X,RU(-1),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL,1,n);
**********
* k=0, s>1, r>1, q_1>1 and p_1>1 (sommetjes equation 7.301)
id GG(R,X,RU(a?{>1},b?,?c),RL(d?{>1},e?,?w),0,n?) = GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),d,n)*den(2)
      +GG(R,X,RU(d,e,?w),RL(b,?c),a,n)*den(2)
      -sum_(jjj,1,1+d,binom_(-jjj+d+a,-1+a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+d,binom_(-jjj+d+a,-1+a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+a,binom_(-jjj+d+a,-1+d)*GG(R(1-jjj+d+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+a,binom_(-jjj+d+a,-1+d)*GG(R(1-jjj+d+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,binom_(-jjj+d+a,d)*GG(R(1-jjj+d+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,binom_(-jjj+d+a,d)*GG(R(1-jjj+d+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,d,binom_(-jjj+d+a,a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,d,binom_(-jjj+d+a,a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1>1 and p_1=1 (sommetjes equation 7.302)
id GG(R,X,RU(1,b?,?c),RL(d?{>1},e?,?w),0,n?) = -GG(R(1+d),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+d),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*d
      -GG(R(1+d),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+d),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n*d
      -GG(R(d),X(2),RU(e,?w),RL(b,?c),2,n)*den(2)*den(2)^(n+1)
      -GG(R(d),X(2),RU(e,?w),RL(b,?c),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(d),X(2),RU(e,?w),RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),1,n)*den(2)
      +GG(R,X,RU(1,b,?c),RL(e,?w),d,n)*den(2)
      -sum_(jjj,1,1+d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*d
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r>1, q_1>1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.303)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{>1},e?{>=0},?w),0,n?) = -binom_(-1+d+abs_(a),-1+d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),-1+d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),d,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1>1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.304)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{>1},e?{>=0},?w),0,n?) = -binom_(-1+d+abs_(a),-1+d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),-1+d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),d,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1>1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.305)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{>1},e?{<0},?w),0,n?) = -binom_(-1+d+abs_(a),-1+d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),-1+d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),d)*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),d)*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n+1)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),d,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1>1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.306)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{>1},e?{<0},?w),0,n?) = -binom_(-1+d+abs_(a),-1+d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),-1+d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),d)*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),d)*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),d,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1>1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.307)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{>1},e?{>=0},?w),0,n?) = GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),d,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*d
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*n*d
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*d
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*n*d
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*d
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r>1, q_1>1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.308)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{>1},e?{>=0},?w),0,n?) = -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*d
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n*d
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),d,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*d
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*n*d
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*d
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r>1, q_1>1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.309)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{>1},e?{<0},?w),0,n?) = -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*d
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n*d
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),d,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*d
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*n*d
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*d
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r>1, q_1>1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.310)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{>1},e?{<0},?w),0,n?) = -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*d
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n*d
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*d
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n*d
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),d,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*d
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n*d;
* k=0, s>1, r>1, q_1=1 and p_1>1 (sommetjes equation 7.311)
id GG(R,X,RU(a?{>1},b?,?c),RL(1,e?,?w),0,n?) = -GG(R(1+a),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -GG(R(1+a),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*a
      -GG(R(1+a),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+a),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n*a
      -GG(R(a),X(2),RU(b,?c),RL(e,?w),2,n)*den(2)*den(2)^(n+1)
      -GG(R(a),X(2),RU(b,?c),RL(e,?w),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(a),X(2),RU(b,?c),RL(1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU(e,?w),RL(b,?c),1+a,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU(e,?w),RL(b,?c),1+a,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R,X,RU(1,e,?w),RL(b,?c),a,n)*den(2)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r>1, q_1=1 and p_1=1 (sommetjes equation 7.312)
id GG(R,X,RU(1,b?,?c),RL(1,e?,?w),0,n?) = -GG(R(1),X(2),RU(b,?c),RL(e,?w),2,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU(b,?c),RL(e,?w),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(1),X(2),RU(e,?w),RL(b,?c),2,n)*den(2)*den(2)^(n+1)
      -GG(R(1),X(2),RU(e,?w),RL(b,?c),2,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)*n
      +GG(R,X,RU(1,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R,X,RU(1,e,?w),RL(b,?c),1,n)*den(2);
* k=0, s>1, r>1, q_1=1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.313)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(1,e?{>=0},?w),0,n?) = -abs_(a)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.314)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(1,e?{>=0},?w),0,n?) = -abs_(a)*GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.315)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(1,e?{<0},?w),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -abs_(a)*den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.316)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(1,e?{<0},?w),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -abs_(a)*GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(a,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.317)
id GG(R,X,RU(-1,b?{>=0},?c),RL(1,e?{>=0},?w),0,n?) = GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)^(n+1)*TT(R(2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)^(n+1)*TT(R(2),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),1,n);
* k=0, s>1, r>1, q_1=1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.318)
id GG(R,X,RU(-1,b?{<0},?c),RL(1,e?{>=0},?w),0,n?) = GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),1,n);
* k=0, s>1, r>1, q_1=1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.319)
id GG(R,X,RU(-1,b?{>=0},?c),RL(1,e?{<0},?w),0,n?) = -GG(R(-2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)^(n+1)*TT(R(2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)^(n+1)*TT(R(2),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),1,n);
* k=0, s>1, r>1, q_1=1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.320)
id GG(R,X,RU(-1,b?{<0},?c),RL(1,e?{<0},?w),0,n?) = -GG(R(-2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)*n
      +den(2)*TT(R,X,RU(1,e,?w),RL(b,?c),1,n);
* k=0, s>1, r>1, q_1<-1, p_1>1, q_2>=0 and p_2>=0 (sommetjes equation 7.321)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),a,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1>1, q_2>=0 and p_2<0 (sommetjes equation 7.322)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),a,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1>1, q_2<0 and p_2>=0 (sommetjes equation 7.323)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = -binom_(-1+a+abs_(d),-1+a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),-1+a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -binom_(-1+a+abs_(d),a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n+1)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),a,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1>1, q_2<0 and p_2<0 (sommetjes equation 7.324)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = -binom_(-1+a+abs_(d),-1+a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),-1+a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -binom_(-1+a+abs_(d),a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -binom_(-1+a+abs_(d),a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),a,n)*den(2)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*den(2)^(n+1)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=1, q_2>=0 and p_2>=0 (sommetjes equation 7.325)
id GG(R,X,RU(1,b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = -abs_(d)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=1, q_2>=0 and p_2<0 (sommetjes equation 7.326)
id GG(R,X,RU(1,b?{<0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=1, q_2<0 and p_2>=0 (sommetjes equation 7.327)
id GG(R,X,RU(1,b?{>=0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = -abs_(d)*GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -abs_(d)*den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=1, q_2<0 and p_2<0 (sommetjes equation 7.328)
id GG(R,X,RU(1,b?{<0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -abs_(d)*GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.329)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.330)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.331)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.332)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)*n
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*den(2)^(n+1)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),abs_(d),n)
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.333)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+e,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.334)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{<-1},e?{>=0},?w),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.335)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1<-1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.336)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{<-1},e?{<0},?w),0,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*TT(R,X,RU(d,e,?w),RL(b,?c),1,n)
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=-1, p_1>1, q_2>=0 and p_2>=0 (sommetjes equation 7.337)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(-1,e?{>=0},?w),0,n?) = GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),a,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*a
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*a
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r>1, q_1=-1, p_1>1, q_2>=0 and p_2<0 (sommetjes equation 7.338)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(-1,e?{>=0},?w),0,n?) = -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*a
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n*a
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),a,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*a
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r>1, q_1=-1, p_1>1, q_2<0 and p_2>=0 (sommetjes equation 7.339)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(-1,e?{<0},?w),0,n?) = -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*a
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n*a
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),a,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*a
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*n*a
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r>1, q_1=-1, p_1>1, q_2<0 and p_2<0 (sommetjes equation 7.340)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(-1,e?{<0},?w),0,n?) = -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*a
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n*a
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*a
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n*a
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),a,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*a
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n*a;
* k=0, s>1, r>1, q_1=-1, p_1=1, q_2>=0 and p_2>=0 (sommetjes equation 7.341)
id GG(R,X,RU(1,b?{>=0},?c),RL(-1,e?{>=0},?w),0,n?) = GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)^(n+1)*TT(R(2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)^(n+1)*TT(R(2),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),1,n);
* k=0, s>1, r>1, q_1=-1, p_1=1, q_2>=0 and p_2<0 (sommetjes equation 7.342)
id GG(R,X,RU(1,b?{<0},?c),RL(-1,e?{>=0},?w),0,n?) = -GG(R(-2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)^(n+1)*TT(R(2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)^(n+1)*TT(R(2),X(2),RU(b,?c),RL(?w),1+e,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(1,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),1,n);
* k=0, s>1, r>1, q_1=-1, p_1=1, q_2<0 and p_2>=0 (sommetjes equation 7.343)
id GG(R,X,RU(1,b?{>=0},?c),RL(-1,e?{<0},?w),0,n?) = GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)^(n+1)*TT(R(-2),X(2),RU(e,?w),RL(?c),1+b,n)*n
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),1,n);
* k=0, s>1, r>1, q_1=-1, p_1=1, q_2<0 and p_2<0 (sommetjes equation 7.344)
id GG(R,X,RU(1,b?{<0},?c),RL(-1,e?{<0},?w),0,n?) = -GG(R(-2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      -GG(R(2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)
      -GG(R(2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n+1)*n
      +GG(R,X,RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)*n
      +den(2)*TT(R,X,RU(1,b,?c),RL(e,?w),1,n);
* k=0, s>1, r>1, q_1=-1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.345)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(-1,e?{>=0},?w),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+b,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=-1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.346)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(-1,e?{>=0},?w),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=-1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.347)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(-1,e?{<0},?w),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=-1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.348)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(-1,e?{<0},?w),0,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n+1)*n
      +GG(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +den(2)*TT(R,X,RU(a,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),abs_(a),n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n+1)*n
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n+1)*n
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n+1)*n;
* k=0, s>1, r>1, q_1=-1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.349)
id GG(R,X,RU(-1,b?{>=0},?c),RL(-1,e?{>=0},?w),0,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,b,?c),RL(?w),1+e,n)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),1,n);
* k=0, s>1, r>1, q_1=-1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.350)
id GG(R,X,RU(-1,b?{<0},?c),RL(-1,e?{>=0},?w),0,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,b,?c),RL(?w),1+e,n)*n
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),1,n);
* k=0, s>1, r>1, q_1=-1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.351)
id GG(R,X,RU(-1,b?{>=0},?c),RL(-1,e?{<0},?w),0,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n+1)*TT(R(1),X(2),RU(-1,e,?w),RL(?c),1+b,n)*n
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),1,n);
* k=0, s>1, r>1, q_1=-1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.352)
id GG(R,X,RU(-1,b?{<0},?c),RL(-1,e?{<0},?w),0,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n+1)*n
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n+1)*n
      +GG(R(1),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)
      +GG(R(1),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n+1)*n
      +den(2)*TT(R,X,RU(-1,b,?c),RL(e,?w),1,n)
      +den(2)*TT(R,X,RU(-1,e,?w),RL(b,?c),1,n);
*--#]

*--#]
.sort
*--#[k=1

*--#[Sign altering
* Case k=1, p_1>=0 and q_1>=0 (sommetjes equation 7.26)
repeat id TT(R,X,RU(e?{>=0},?a),RL(c?{>=0},?b),1,n?) = sign(n)*den(n+1)*(TT(R,X,RU(c,?b),RL(?a),e,n) 
        - sign(n)*TT(R,X,RU(e,?a),RL(?b),c,n)) 
        + TT(R,X,RU(e,?a),RL(?b),c+1,n);
* Case k=1, p_1>=0 and q_1<0 (sommetjes equation 7.27) 
repeat id TT(R,X,RU(e?{>=0},?a),RL(c?{<0},?b),1,n?) = sign(n)*den(n+1)*(TT(R,X,RU(c,?b),RL(?a),e,n) - sign(n)*GG(R,X,RU(e,?a),RL(?b),abs_(c),n)) 
        + GG(R,X,RU(e,?a),RL(?b),abs_(c)+1,n);
* Case k=1, p_1<0 and q_1>=0 (sommetjes equation 7.28) 
repeat id TT(R,X,RU(e?{<0},?a),RL(c?{>=0},?b),1,n?) = sign(n)*den(n+1)*(GG(R,X,RU(c,?b),RL(?a),abs_(e),n) - sign(n)*TT(R,X,RU(e,?a),RL(?b),c,n)) 
        + TT(R,X,RU(e,?a),RL(?b),c+1,n);
* Case k=1, p_1<0 and q_1<0 (sommetjes equation 7.29) 
repeat id TT(R,X,RU(e?{<0},?a),RL(c?{<0},?b),1,n?) = sign(n)*den(n+1)*(GG(R,X,RU(c,?b),RL(?a),abs_(e),n) - sign(n)*GG(R,X,RU(e,?a),RL(?b),abs_(c),n)) 
        + GG(R,X,RU(e,?a),RL(?b),abs_(c)+1,n);
*--#]

*--#[Fixed sign
* k=1, s=1, r=1, q_1>1 and p_1>1 (sommetjes equation 7.105) 
id GG(R,X,RU(a?{>1}),RL(b?{>1}),1,n?) = GG(R(a),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n)
      +GG(R(b),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a),RL,b,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL,1+b,n)
      +sum_(jjj,1,-1+b,GG(R(1-jjj+b),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(1-jjj+b+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1>1 and p_1=1 (sommetjes equation 7.106)
id GG(R,X,RU(1),RL(b?{>1}),1,n?) = -GG(R(1+b),X(2),RU,RL,1,n)*den(2)*den(2)^(n)
      -GG(R(1+b),X(2),RU,RL,1,n)*den(2)*den(2)^(n)*b
      +GG(R(b),X(2),RU,RL(1),1,n)*den(2)*den(2)^(n)
      -GG(R(b),X(2),RU,RL,2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(1),RL,1+b,n)
      -sum_(jjj,1,1+b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)*b;
* k=1, s=1, r=1, q_1>1 and p_1<-1 (sommetjes equation 7.107) 
id GG(R,X,RU(a?{<-1}),RL(b?{>1}),1,n?) = binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n)*S(R(-1-b-abs_(a)),X(2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n)*S(R(1+b+abs_(a)),X(2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n)*S(R(-1-b-abs_(a)),X(2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n)*S(R(1+b+abs_(a)),X(2),n)
      +GG(R(b),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL,1+b,n)
      +den(2)*den(2)^(n)*S(R(1+b+abs_(a)),X(2),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(a),b),X(2,1),n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU,RL,1+b,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1>1 and p_1=-1 (sommetjes equation 7.108)
id GG(R,X,RU(-1),RL(b?{>1}),1,n?) = GG(R(b),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1),RL,1+b,n)
      +den(2)*den(2)^(n)*S(R(-2-b),X(2),n)
      +den(2)*den(2)^(n)*S(R(-2-b),X(2),n)*b
      +2*den(2)*den(2)^(n)*S(R(2+b),X(2),n)
      +den(2)*den(2)^(n)*S(R(2+b),X(2),n)*b
      -den(2)*den(2)^(n)*S(R(2,b),X(2,1),n)
      -den(2)*den(2)^(n)*TT(R(b),X(2),RU,RL,2,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)*b;
* k=1, s=1, r=1, q_1=1 and p_1>1 (sommetjes equation 7.109) 
id GG(R,X,RU(a?{>1}),RL(1),1,n?) = -GG(R(1+a),X(2),RU,RL,1,n)*den(2)*den(2)^(n)
      -GG(R(1+a),X(2),RU,RL,1,n)*den(2)*den(2)^(n)*a
      +GG(R(a),X(2),RU,RL(1),1,n)*den(2)*den(2)^(n)
      -GG(R(a),X(2),RU,RL,2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL,2,n)
      -sum_(jjj,1,1+a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s=1, r=1, q_1=1 and p_1=1 (sommetjes equation 7.110)
id GG(R,X,RU(1),RL(1),1,n?) = GG(R(1),X(2),RU(1),RL,1,n)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(1),1,n)*den(2)^(n)
      -GG(R(1),X(2),RU,RL,2,n)*den(2)^(n)
      -2*GG(R(2),X(2),RU,RL,1,n)*den(2)^(n)
      +GG(R,X,RU(1),RL,2,n);
* k=1, s=1, r=1, q_1=1 and p_1<-1 (sommetjes equation 7.111) 
id GG(R,X,RU(a?{<-1}),RL(1),1,n?) = abs_(a)*den(2)*den(2)^(n)*S(R(-2-abs_(a)),X(2),n)
      +abs_(a)*den(2)*den(2)^(n)*S(R(2+abs_(a)),X(2),n)
      +GG(R(1),X(2),RU(a),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL,2,n)
      +den(2)*den(2)^(n)*S(R(-2-abs_(a)),X(2),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(a),1),X(2,1),n)
      +2*den(2)*den(2)^(n)*S(R(2+abs_(a)),X(2),n)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1=1 and p_1=-1 (sommetjes equation 7.112)
id GG(R,X,RU(-1),RL(1),1,n?) = GG(R(1),X(2),RU(-1),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1),RL,2,n)
      +den(2)^(n)*S(R(-3),X(2),n)
      -den(2)*den(2)^(n)*S(R(2,1),X(2,1),n)
      +3*den(2)*den(2)^(n)*S(R(3),X(2),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU,RL,2,n);
* k=1, s=1, r=1, q_1<-1 and p_1>1 (sommetjes equation 7.113) 
id GG(R,X,RU(a?{>1}),RL(b?{<-1}),1,n?) = binom_(-1+a+abs_(b),-1+a)*den(2)*den(2)^(n)*S(R(-1-a-abs_(b)),X(2),n)
      +binom_(-1+a+abs_(b),-1+a)*den(2)*den(2)^(n)*S(R(1+a+abs_(b)),X(2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n)*S(R(-1-a-abs_(b)),X(2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n)*S(R(1+a+abs_(b)),X(2),n)
      +GG(R(a),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*S(R(1+a+abs_(b)),X(2),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(b),a),X(2,1),n)
      +den(2)*den(2)^(n)*TT(R(-abs_(b)),X(2),RU,RL,1+a,n)
      +TT(R,X,RU(a),RL,1+abs_(b),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1<-1 and p_1=1 (sommetjes equation 7.114)
id GG(R,X,RU(1),RL(b?{<-1}),1,n?) = abs_(b)*den(2)*den(2)^(n)*S(R(-2-abs_(b)),X(2),n)
      +abs_(b)*den(2)*den(2)^(n)*S(R(2+abs_(b)),X(2),n)
      +GG(R(1),X(2),RU(b),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(b),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*S(R(-2-abs_(b)),X(2),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(b),1),X(2,1),n)
      +2*den(2)*den(2)^(n)*S(R(2+abs_(b)),X(2),n)
      +TT(R,X,RU(1),RL,1+abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*abs_(b)*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1<-1 and p_1<-1 (sommetjes equation 7.115) 
id GG(R,X,RU(a?{<-1}),RL(b?{<-1}),1,n?) = GG(R(-abs_(a)),X(2),RU,RL,1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(-abs_(b)),X(2),RU,RL,1+abs_(a),n)*den(2)*den(2)^(n)
      +2*den(2)*den(2)^(n)*S(R(-1-abs_(a)-abs_(b)),X(2),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(a),b),X(2,1),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(b),a),X(2,1),n)
      +TT(R,X,RU(a),RL,1+abs_(b),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1<-1 and p_1=-1 (sommetjes equation 7.116)
id GG(R,X,RU(-1),RL(b?{<-1}),1,n?) = -abs_(b)*GG(R(-1-abs_(b)),X(2),RU,RL,1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(b)),X(2),RU,RL,1,n)*den(2)*den(2)^(n)
      +den(2)^(n)*S(R(-2-abs_(b)),X(2),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(b),-1),X(2,1),n)
      -den(2)*den(2)^(n)*S(R(2,b),X(2,1),n)
      +TT(R,X,RU(-1),RL,abs_(b)+1,n)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n))*abs_(b)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1=-1 and p_1>1 (sommetjes equation 7.117) 
id GG(R,X,RU(a?{>1}),RL(-1),1,n?) = GG(R(a),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*S(R(-2-a),X(2),n)
      +den(2)*den(2)^(n)*S(R(-2-a),X(2),n)*a
      +2*den(2)*den(2)^(n)*S(R(2+a),X(2),n)
      +den(2)*den(2)^(n)*S(R(2+a),X(2),n)*a
      -den(2)*den(2)^(n)*S(R(2,a),X(2,1),n)
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU,RL,2,n)
      +TT(R,X,RU(a),RL,2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s=1, r=1, q_1=-1 and p_1=1 (sommetjes equation 7.118)
id GG(R,X,RU(1),RL(-1),1,n?) = GG(R(1),X(2),RU(-1),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(-1),1,n)*den(2)*den(2)^(n)
      +2*den(2)*den(2)^(n)*S(R(-3),X(2),n)
      -den(2)*den(2)^(n)*S(R(2,1),X(2,1),n)
      +3*den(2)*den(2)^(n)*S(R(3),X(2),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU,RL,2,n)
      +TT(R,X,RU(1),RL,2,n);
* k=1, s=1, r=1, q_1=-1 and p_1<-1 (sommetjes equation 7.119) 
id GG(R,X,RU(a?{<-1}),RL(-1),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL,1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU,RL,1,n)*den(2)*den(2)^(n)
      +den(2)^(n)*S(R(-2-abs_(a)),X(2),n)
      -den(2)*den(2)^(n)*S(R(1+abs_(a),-1),X(2,1),n)
      -den(2)*den(2)^(n)*S(R(2,a),X(2,1),n)
      +TT(R,X,RU(a),RL,2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r=1, q_1=-1 and p_1=-1 (sommetjes equation 7.120)
id GG(R,X,RU(-1),RL(-1),1,n?) = -2*GG(R(-2),X(2),RU,RL,1,n)*den(2)^(n)
      -den(2)^(n)*S(R(2,-1),X(2,1),n)
      +den(2)^(n)*S(R(-3),X(2),n)
      +TT(R,X,RU(-1),RL,2,n);
*********
* k=1, s=1, r>1, q_1>1 and p_1>1 (sommetjes equation 7.121) 
id GG(R,X,RU(a?{>1}),RL(b?{>1},c?,?d),1,n?) = GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL(c,?d),1+b,n)
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(1-jjj+b+a),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(1-jjj+b+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(1-jjj+b+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(1-jjj+b+a),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1>1 and p_1=1 (sommetjes equation 7.122)
id GG(R,X,RU(1),RL(b?{>1},c?,?d),1,n?) = -GG(R(1+b),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(1+b),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n)*b
      +GG(R(b),X(2),RU(c,?d),RL(1),1,n)*den(2)*den(2)^(n)
      -GG(R(b),X(2),RU(c,?d),RL,2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(1),RL(c,?d),1+b,n)
      -sum_(jjj,1,1+b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,b,GG(R(2-jjj+b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)*b;
* k=1, s=1, r>1, q_1>1, p_1<-1 and q_2>=0 (sommetjes equation 7.123)
id GG(R,X,RU(a?{<-1}),RL(b?{>1},c?{>=0},?d),1,n?) = -binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+c+b+abs_(a),?d),X(2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      -binom_(-1+b+abs_(a),abs_(a))*den(2)*den(2)^(n)*TT(R(-b-abs_(a)),X(2),RU,RL(?d),1+c,n)
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+c+b+abs_(a),?d),X(2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n)*TT(R(-b-abs_(a)),X(2),RU,RL(?d),1+c,n)
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL(c,?d),1+b,n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU,RL(c,?d),1+b,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1>1, p_1<-1 and q_2<0 (sommetjes equation 7.124)
id GG(R,X,RU(a?{<-1}),RL(b?{>1},c?{<0},?d),1,n?) = -binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-1-b-abs_(a)-abs_(c),?d),X(2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      -binom_(-1+b+abs_(a),abs_(a))*GG(R(-b-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -binom_(-1+b+abs_(a),b)*GG(R(-b-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-1-b-abs_(a)-abs_(c),?d),X(2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      +GG(R(b),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL(c,?d),1+b,n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+b+abs_(a),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU,RL(c,?d),1+b,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(1-jjj+b+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(-1+jjj-b-abs_(a)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1>1, p_1=-1 and q_2>=0 (sommetjes equation 7.125)
id GG(R,X,RU(-1),RL(b?{>1},c?{>=0},?d),1,n?) = GG(R(b),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1),RL(c,?d),1+b,n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+c+b,?d),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+c+b,?d),X(2),n)*b
      +2*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*b
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n)*TT(R(-1-b),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n)*TT(R(-1-b),X(2),RU,RL(?d),1+c,n)*b
      -den(2)*den(2)^(n)*TT(R(b),X(2),RU(c,?d),RL,2,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)*b;
* k=1, s=1, r>1, q_1>1, p_1=-1 and q_2<0 (sommetjes equation 7.126)
id GG(R,X,RU(-1),RL(b?{>1},c?{<0},?d),1,n?) = -GG(R(-1-b),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -GG(R(-1-b),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)*b
      +GG(R(b),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1),RL(c,?d),1+b,n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-b-abs_(c),?d),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-b-abs_(c),?d),X(2),n)*b
      +2*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+b,c,?d),X(2,1),n)*b
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n)*TT(R(b),X(2),RU(c,?d),RL,2,n)
      +sum_(jjj,1,b,GG(R(1-jjj+b),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,b,TT(R(-2+jjj-b),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)*b;
* k=1, s=1, r>1, q_1=1 and p_1>1 (sommetjes equation 7.127)
id GG(R,X,RU(a?{>1}),RL(1,c?,?d),1,n?) = -GG(R(1+a),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n)
      -GG(R(1+a),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n)*a
      -GG(R(a),X(2),RU,RL(c,?d),2,n)*den(2)*den(2)^(n)
      +GG(R(a),X(2),RU,RL(1,c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU(c,?d),RL,1+a,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL(c,?d),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s=1, r>1, q_1=1 and p_1=1 (sommetjes equation 7.128)
id GG(R,X,RU(1),RL(1,c?,?d),1,n?) = GG(R(1),X(2),RU(c,?d),RL(1),1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU(c,?d),RL,2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1),RL(c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,c,?d),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU,RL(c,?d),2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(1,c,?d),1,n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU(c,?d),RL,1,n)*den(2)^(n)
      -GG(R(2),X(2),RU,RL(c,?d),1,n)*den(2)^(n)
      +GG(R,X,RU(1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=1, p_1<-1 and q_2>=0 (sommetjes equation 7.129)
id GG(R,X,RU(a?{<-1}),RL(1,c?{>=0},?d),1,n?) = -abs_(a)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+c+abs_(a),?d),X(2),n)
      +(abs_(a)+2)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+abs_(a),c,?d),X(2,1),n)
      -abs_(a)*den(2)*den(2)^(n)*TT(R(-1-abs_(a)),X(2),RU,RL(?d),1+c,n)
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL(c,?d),2,n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+c+abs_(a),?d),X(2),n)
      -den(2)*den(2)^(n)*TT(R(-1-abs_(a)),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(c,?d),RL,1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1=1, p_1<-1 and q_2<0 (sommetjes equation 7.130)
id GG(R,X,RU(a?{<-1}),RL(1,c?{<0},?d),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -abs_(a)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-abs_(a)-abs_(c),?d),X(2),n)
      +(abs_(a)+2)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+abs_(a),c,?d),X(2,1),n)
      -GG(R(-1-abs_(a)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a),RL(c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(c,?d),RL(a),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a),RL(c,?d),2,n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-abs_(a)-abs_(c),?d),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),1,c,?d),X(2,1,1),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(c,?d),RL,1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1=1, p_1=-1 and q_2>=0 (sommetjes equation 7.131)
id GG(R,X,RU(-1),RL(1,c?{>=0},?d),1,n?) = GG(R(1),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1),RL(c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1),RL(c,?d),2,n)
      -den(2)^(n)*TT(R(-2),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,1,c,?d),X(2,1,1),n)
      +3*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(3,c,?d),X(2,1),n)
      -2*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(c+3,?d),X(2),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(c,?d),RL,2,n);
* k=1, s=1, r>1, q_1=1, p_1=-1 and q_2<0 (sommetjes equation 7.132)
id GG(R,X,RU(-1),RL(1,c?{<0},?d),1,n?) = -GG(R(-2),X(2),RU,RL(?d),1+abs_(c),n)*den(2)^(n)
      +GG(R(1),X(2),RU(c,?d),RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1),RL(c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1),RL(c,?d),2,n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,1,c,?d),X(2,1,1),n)
      +3*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(3,c,?d),X(2,1),n)
      -2*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(abs_(c)+3),?d),X(2),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(c,?d),RL,2,n);
* k=1, s=1, r>1, q_1<-1, p_1>1 and q_2>=0 (sommetjes equation 7.133)
id GG(R,X,RU(a?{>1}),RL(b?{<-1},c?{>=0},?d),1,n?) = -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-1-c-a-abs_(b),?d),X(2),n)
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-1-a-abs_(b),c,?d),X(2,1),n)
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n)*TT(R(a+abs_(b)),X(2),RU,RL(?d),1+c,n)
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(1+c+a+abs_(b)),?d),X(2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(1+a+abs_(b)),c,?d),X(2,1),n)
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n)*TT(R(a+abs_(b)),X(2),RU,RL(?d),1+c,n)
      +GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(-abs_(b)),X(2),RU(c,?d),RL,1+a,n)
      +den(2)*den(2)^(n)*TT(R(abs_(b)),X(2),RU(a),RL(?d),1+c,n)
      +TT(R,X,RU(a),RL(c,?d),1+abs_(b),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1<-1, p_1>1 and q_2<0 (sommetjes equation 7.134)
id GG(R,X,RU(a?{>1}),RL(b?{<-1},c?{<0},?d),1,n?) = -binom_(-1+a+abs_(b),abs_(b))*GG(R(a+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-1-a-abs_(b),c,?d),X(2,1),n)
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+a+abs_(b)+abs_(c),?d),X(2),n)
      -binom_(-1+a+abs_(b),a)*GG(R(a+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+a+abs_(b)+abs_(c),?d),X(2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(1+a+abs_(b)),c,?d),X(2,1),n)
      +GG(R(abs_(b)),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +GG(R(a),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(-abs_(b)),X(2),RU(c,?d),RL,1+a,n)
      +TT(R,X,RU(a),RL(c,?d),1+abs_(b),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(1-jjj+a+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(-1+jjj-a-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1<-1, p_1=1 and q_2>=0 (sommetjes equation 7.135)
id GG(R,X,RU(1),RL(b?{<-1},c?{>=0},?d),1,n?) = -(abs_(b)+1)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(2+c+abs_(b)),?d),X(2),n)
      +(abs_(b)+1)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      -abs_(b)*den(2)*den(2)^(n)*TT(R(1+abs_(b)),X(2),RU,RL(?d),1+c,n)
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(1+abs_(b)),X(2),RU,RL(?d),1+c,n)
      +den(2)*den(2)^(n)*TT(R(abs_(b)),X(2),RU(1),RL(?d),1+c,n)
      +TT(R,X,RU(1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1<-1, p_1=1 and q_2<0 (sommetjes equation 7.136)
id GG(R,X,RU(1),RL(b?{<-1},c?{<0},?d),1,n?) = -abs_(b)*GG(R(1+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -(abs_(b)+1)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(-2-abs_(b)-abs_(c)),?d),X(2),n)
      +(abs_(b)+1)*den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      -GG(R(1+abs_(b)),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +GG(R(abs_(b)),X(2),RU(1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,c,?d),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(b,c,?d),1,n)*den(2)*den(2)^(n)
      +TT(R,X,RU(1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(1),RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(2-jjj+abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1<-1, p_1<-1 and q_2>=0 (sommetjes equation 7.137)
id GG(R,X,RU(a?{<-1}),RL(b?{<-1},c?{>=0},?d),1,n?) = GG(R(-abs_(a)),X(2),RU,RL(c,?d),1+abs_(b),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-1-abs_(a)-abs_(b),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*GG(R(-abs_(b)),X(2),RU(c,?d),RL,1+abs_(a),n)
      +den(2)*den(2)^(n)*TT(R(abs_(b)),X(2),RU(a),RL(?d),1+c,n)
      +TT(R,X,RU(a),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1<-1, p_1<-1 and q_2<0 (sommetjes equation 7.138)
id GG(R,X,RU(a?{<-1}),RL(b?{<-1},c?{<0},?d),1,n?) = GG(R(-abs_(a)),X(2),RU,RL(c,?d),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(abs_(b)),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-1-abs_(a)-abs_(b),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),b,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*GG(R(-abs_(b)),X(2),RU(c,?d),RL,1+abs_(a),n)
      +TT(R,X,RU(a),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(b,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(a),RL(c,?d),jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1<-1, p_1=-1 and q_2>=0 (sommetjes equation 7.139)
id GG(R,X,RU(-1),RL(b?{<-1},c?{>=0},?d),1,n?) = -abs_(b)*GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(abs_(b)),X(2),RU(-1),RL(?d),1+c,n)
      +TT(R,X,RU(-1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1<-1, p_1=-1 and q_2<0 (sommetjes equation 7.140)
id GG(R,X,RU(-1),RL(b?{<-1},c?{<0},?d),1,n?) = -abs_(b)*GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(b)),X(2),RU(c,?d),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(abs_(b)),X(2),RU(-1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-(2+abs_(b)),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,b,c,?d),X(2,1,1),n)
      +TT(R,X,RU(-1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(b),GG(R(-2+jjj-abs_(b)),X(2),RU,RL(c,?d),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(b),TT(R(1-jjj+abs_(b)),X(2),RU(-1),RL(c,?d),jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1=-1, p_1>1 and q_2>=0 (sommetjes equation 7.141)
id GG(R,X,RU(a?{>1}),RL(-1,c?{>=0},?d),1,n?) = GG(R(a),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-c-a,?d),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-c-a,?d),X(2),n)*a
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*a
      -den(2)*den(2)^(n)*TT(R(1+a),X(2),RU,RL(?d),1+c,n)
      -den(2)*den(2)^(n)*TT(R(1+a),X(2),RU,RL(?d),1+c,n)*a
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU,RL(c,?d),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(a),RL(?d),1+c,n)
      +TT(R,X,RU(a),RL(c,?d),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s=1, r>1, q_1=-1, p_1>1 and q_2<0 (sommetjes equation 7.142)
id GG(R,X,RU(a?{>1}),RL(-1,c?{<0},?d),1,n?) = -GG(R(1+a),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -GG(R(1+a),X(2),RU,RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)*a
      +GG(R(a),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-a,c,?d),X(2,1),n)*a
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+a+abs_(c),?d),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2+a+abs_(c),?d),X(2),n)*a
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU,RL(c,?d),2,n)
      +TT(R,X,RU(a),RL(c,?d),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s=1, r>1, q_1=-1, p_1=1 and q_2>=0 (sommetjes equation 7.143)
id GG(R,X,RU(1),RL(-1,c?{>=0},?d),1,n?) = GG(R(1),X(2),RU(-1,c,?d),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n)
      -den(2)^(n)*g(nargs_(?d))*S(R(-3-c,?d),X(2),n)
      +den(2)^(n)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      -den(2)^(n)*TT(R(2),X(2),RU,RL(?d),1+c,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(1),RL(?d),1+c,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU,RL(c,?d),2,n)
      +TT(R,X,RU(1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=-1, p_1=1 and q_2<0 (sommetjes equation 7.144)
id GG(R,X,RU(1),RL(-1,c?{<0},?d),1,n?) = GG(R(1),X(2),RU(-1,c,?d),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(-1,c,?d),1,n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU,RL(?d),1+abs_(c),n)*den(2)^(n)
      -den(2)^(n)*g(nargs_(?d))*S(R(3+abs_(c),?d),X(2),n)
      +den(2)^(n)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU,RL(c,?d),2,n)
      +TT(R,X,RU(1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=-1, p_1<-1 and q_2>=0 (sommetjes equation 7.145)
id GG(R,X,RU(a?{<-1}),RL(-1,c?{>=0},?d),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-abs_(a),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),-1,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(a),RL(?d),1+c,n)
      +TT(R,X,RU(a),RL(c,?d),2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1=-1, p_1<-1 and q_2<0 (sommetjes equation 7.146)
id GG(R,X,RU(a?{<-1}),RL(-1,c?{<0},?d),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU,RL(c,?d),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-2-abs_(a),c,?d),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(1+abs_(a),-1,c,?d),X(2,1,1),n)
      +TT(R,X,RU(a),RL(c,?d),2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(c,?d),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,c,?d),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s=1, r>1, q_1=-1, p_1=-1 and q_2>=0 (sommetjes equation 7.147)
id GG(R,X,RU(-1),RL(-1,c?{>=0},?d),1,n?) = -GG(R(-2),X(2),RU,RL(c,?d),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(c,?d),RL,1,n)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,-1,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(-1),RL(?d),1+c,n)
      +TT(R,X,RU(-1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=-1, p_1=-1 and q_2<0 (sommetjes equation 7.148)
id GG(R,X,RU(-1),RL(-1,c?{<0},?d),1,n?) = -GG(R(-2),X(2),RU,RL(c,?d),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(c,?d),RL,1,n)*den(2)^(n)
      +GG(R(1),X(2),RU(-1),RL(?d),1+abs_(c),n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?d))*S(R(2,-1,c,?d),X(2,1,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?d))*S(R(-3,c,?d),X(2,1),n)
      +TT(R,X,RU(-1),RL(c,?d),2,n);
**********
* k=1, s>1, r=1, q_1>1 and p_1>1 (sommetjes equation 7.149) 
id GG(R,X,RU(a?{>1},b?,?c),RL(d?{>1}),1,n?) = GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n)
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d),RL(b,?c),a,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL,d,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL,1+d,n)
      +sum_(jjj,1,-1+d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,-1+a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+d,GG(R(1-jjj+d+a),X(2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+a,-1+a))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+a,GG(R(1-jjj+d+a),X(2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+a,-1+d))*den(2)*den(2)^(n)
      -sum_(jjj,1,a,GG(R(1-jjj+d+a),X(2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+a,d))*den(2)*den(2)^(n)
      -sum_(jjj,1,d,GG(R(1-jjj+d+a),X(2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+a,a))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1>1 and p_1=1 (sommetjes equation 7.150)
id GG(R,X,RU(1,b?,?c),RL(d?{>1}),1,n?) = -GG(R(1+d),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(1+d),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n)*d
      -GG(R(d),X(2),RU,RL(b,?c),2,n)*den(2)*den(2)^(n)
      +GG(R(d),X(2),RU,RL(1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU(b,?c),RL,1+d,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(1,b,?c),RL,1+d,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r=1, q_1>1, p_1<-1 and p_2>=0 (sommetjes equation 7.151)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{>1}),1,n?) = -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n)*S(R(-1-d-b-abs_(a),?c),X(2),n)*g(nargs_(?c))
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n)*S(R(-1-d-abs_(a),b,?c),X(2,1),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n)*TT(R(d+abs_(a)),X(2),RU,RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*S(R(-(1+d+b+abs_(a)),?c),X(2),n)*g(nargs_(?c))
      +binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*S(R(-(1+d+abs_(a)),b,?c),X(2,1),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*TT(R(d+abs_(a)),X(2),RU,RL(?c),1+b,n)
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL,1+d,n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU(b,?c),RL,1+d,n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(d),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+d,TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),-1+abs_(a)))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),-1+d))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),d))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),abs_(a)))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1>1, p_1<-1 and p_2<0 (sommetjes equation 7.152)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{>1}),1,n?) = -binom_(-1+d+abs_(a),abs_(a))*GG(R(d+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n)*S(R(-1-d-abs_(a),b,?c),X(2,1),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n)*S(R(1+d+abs_(a)+abs_(b),?c),X(2),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*S(R(-(-1-d-abs_(a)-abs_(b)),?c),X(2),n)*g(nargs_(?c))
      +binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*S(R(-(1+d+abs_(a)),b,?c),X(2,1),n)*g(nargs_(?c))
      +GG(R(abs_(a)),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(d),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL,1+d,n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU(b,?c),RL,1+d,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+d,TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),-1+abs_(a)))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),-1+d))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(1-jjj+d+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),d))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),abs_(a)))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1>1, p_1=-1 and p_2>=0 (sommetjes equation 7.153)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{>1}),1,n?) = GG(R(d),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL,1+d,n)
      +den(2)*den(2)^(n)*S(R(-2-d,b,?c),X(2,1),n)*g(nargs_(?c))
      +den(2)*den(2)^(n)*S(R(-2-d,b,?c),X(2,1),n)*d*g(nargs_(?c))
      -den(2)*den(2)^(n)*S(R(-2-d-b,?c),X(2),n)*g(nargs_(?c))
      -den(2)*den(2)^(n)*S(R(-2-d-b,?c),X(2),n)*d*g(nargs_(?c))
      -den(2)*den(2)^(n)*TT(R(1+d),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1+d),X(2),RU,RL(?c),1+b,n)*d
      -den(2)*den(2)^(n)*TT(R(d),X(2),RU,RL(b,?c),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(d),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r=1, q_1>1, p_1=-1 and p_2<0 (sommetjes equation 7.154)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{>1}),1,n?) = -GG(R(1+d),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(1+d),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)*d
      +GG(R(d),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL,1+d,n)
      +den(2)*den(2)^(n)*S(R(-2-d,b,?c),X(2,1),n)*g(nargs_(?c))
      +den(2)*den(2)^(n)*S(R(-2-d,b,?c),X(2,1),n)*d*g(nargs_(?c))
      -den(2)*den(2)^(n)*S(R(2+d+abs_(b),?c),X(2),n)*g(nargs_(?c))
      -den(2)*den(2)^(n)*S(R(2+d+abs_(b),?c),X(2),n)*d*g(nargs_(?c))
      -den(2)*den(2)^(n)*TT(R(d),X(2),RU,RL(b,?c),2,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r=1, q_1=1 and p_1>1 (sommetjes equation 7.155)
id GG(R,X,RU(a?{>1},b?,?c),RL(1),1,n?) = -GG(R(1+a),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(1+a),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n)*a
      +GG(R(a),X(2),RU(b,?c),RL(1),1,n)*den(2)*den(2)^(n)
      -GG(R(a),X(2),RU(b,?c),RL,2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL,2,n)
      -sum_(jjj,1,1+a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r=1, q_1=1 and p_1=1 (sommetjes equation 7.156)
id GG(R,X,RU(1,b?,?c),RL(1),1,n?) = GG(R(1),X(2),RU(b,?c),RL(1),1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU(b,?c),RL,2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,b,?c),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU,RL(b,?c),2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(1,b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU(b,?c),RL,1,n)*den(2)^(n)
      -GG(R(2),X(2),RU,RL(b,?c),1,n)*den(2)^(n)
      +GG(R,X,RU(1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=1, p_1<-1 and p_2>=0 (sommetjes equation 7.157)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(1),1,n?) = -abs_(a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-(2+b+abs_(a)),?c),X(2),n)
      +abs_(a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      -abs_(a)*den(2)*den(2)^(n)*TT(R(1+abs_(a)),X(2),RU,RL(?c),1+b,n)
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL,2,n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-b-abs_(a),?c),X(2),n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-abs_(a),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*TT(R(1+abs_(a)),X(2),RU,RL(?c),1+b,n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(1),RL(?c),1+b,n)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1=1, p_1<-1 and p_2<0 (sommetjes equation 7.158)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(1),1,n?) = -abs_(a)*GG(R(1+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -abs_(a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-(-2-abs_(a)-abs_(b)),?c),X(2),n)
      +abs_(a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      -GG(R(1+abs_(a)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(abs_(a)),X(2),RU(1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL,2,n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-abs_(a),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+abs_(a)+abs_(b),?c),X(2),n)
      -sum_(jjj,2,1+abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1=1, p_1=-1 and p_2>=0 (sommetjes equation 7.159)
id GG(R,X,RU(-1,b?{>=0},?c),RL(1),1,n?) = GG(R(1),X(2),RU(-1,b,?c),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL,2,n)
      -den(2)^(n)*g(nargs_(?c))*S(R(-3-b,?c),X(2),n)
      +den(2)^(n)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      -den(2)^(n)*TT(R(2),X(2),RU,RL(?c),1+b,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(1),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU,RL(b,?c),2,n);
* k=1, s>1, r=1, q_1=1, p_1=-1 and p_2<0 (sommetjes equation 7.160)
id GG(R,X,RU(-1,b?{<0},?c),RL(1),1,n?) = GG(R(1),X(2),RU(-1,b,?c),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU,RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU,RL(?c),1+abs_(b),n)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL,2,n)
      -den(2)^(n)*g(nargs_(?c))*S(R(3+abs_(b),?c),X(2),n)
      +den(2)^(n)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU,RL(b,?c),2,n);
* k=1, s>1, r=1, q_1<-1, p_1>1 and p_2>=0 (sommetjes equation 7.161)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(d?{<-1}),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+b+a+abs_(d),?c),X(2),n)
      +binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n)*TT(R(-a-abs_(d)),X(2),RU,RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+b+a+abs_(d),?c),X(2),n)
      +binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*TT(R(-a-abs_(d)),X(2),RU,RL(?c),1+b,n)
      +GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(-abs_(d)),X(2),RU,RL(b,?c),1+a,n)
      +TT(R,X,RU(a,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1<-1, p_1>1 and p_2<0 (sommetjes equation 7.162)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(d?{<-1}),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-1-a-abs_(b)-abs_(d),?c),X(2),n)
      +binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-1-a-abs_(b)-abs_(d),?c),X(2),n)
      +binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      +GG(R(a),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+a+abs_(d),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(-abs_(d)),X(2),RU,RL(b,?c),1+a,n)
      +TT(R,X,RU(a,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1<-1, p_1=1 and p_2>=0 (sommetjes equation 7.163)
id GG(R,X,RU(1,b?{>=0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+b+abs_(d),?c),X(2),n)
      +(abs_(d)+2)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+abs_(d),b,?c),X(2,1),n)
      -abs_(d)*den(2)*den(2)^(n)*TT(R(-1-abs_(d)),X(2),RU,RL(?c),1+b,n)
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+b+abs_(d),?c),X(2),n)
      -den(2)*den(2)^(n)*TT(R(-1-abs_(d)),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL,1+abs_(d),n)
      +TT(R,X,RU(1,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1<-1, p_1=1 and p_2<0 (sommetjes equation 7.164)
id GG(R,X,RU(1,b?{<0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -abs_(d)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-abs_(b)-abs_(d),?c),X(2),n)
      +(abs_(d)+2)*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+abs_(d),b,?c),X(2,1),n)
      -GG(R(-1-abs_(d)),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(d),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-abs_(b)-abs_(d),?c),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),1,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL,1+abs_(d),n)
      +TT(R,X,RU(1,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1<-1, p_1<-1 and p_2>=0 (sommetjes equation 7.165)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{<-1}),1,n?) = GG(R(-abs_(d)),X(2),RU,RL(b,?c),1+abs_(a),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-1-abs_(a)-abs_(d),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*GG(R(-abs_(a)),X(2),RU(b,?c),RL,1+abs_(d),n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(d),RL(?c),1+b,n)
      +TT(R,X,RU(a,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1<-1, p_1<-1 and p_2<0 (sommetjes equation 7.166)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{<-1}),1,n?) = GG(R(abs_(a)),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(-abs_(d)),X(2),RU,RL(b,?c),1+abs_(a),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-1-abs_(a)-abs_(d),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),a,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*GG(R(-abs_(a)),X(2),RU(b,?c),RL,1+abs_(d),n)
      +TT(R,X,RU(a,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1<-1, p_1=-1 and p_2>=0 (sommetjes equation 7.167)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-abs_(d),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),-1,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(d),RL(?c),1+b,n)
      +TT(R,X,RU(-1,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1<-1, p_1=-1 and p_2<0 (sommetjes equation 7.168)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(d)),X(2),RU,RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-abs_(d),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(1+abs_(d),-1,b,?c),X(2,1,1),n)
      +TT(R,X,RU(-1,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL,jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL,jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1=-1, p_1>1 and p_2>=0 (sommetjes equation 7.169)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(-1),1,n?) = GG(R(a),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+b+a,?c),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+b+a,?c),X(2),n)*a
      +2*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*a
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n)*TT(R(-1-a),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(-1-a),X(2),RU,RL(?c),1+b,n)*a
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU(b,?c),RL,2,n)
      +TT(R,X,RU(a,b,?c),RL,2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r=1, q_1=-1, p_1>1 and p_2<0 (sommetjes equation 7.170)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(-1),1,n?) = -GG(R(-1-a),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(-1-a),X(2),RU,RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)*a
      +GG(R(a),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-a-abs_(b),?c),X(2),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-2-a-abs_(b),?c),X(2),n)*a
      +2*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2+a,b,?c),X(2,1),n)*a
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU(b,?c),RL,2,n)
      +TT(R,X,RU(a,b,?c),RL,2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r=1, q_1=-1, p_1=1 and p_2>=0 (sommetjes equation 7.171)
id GG(R,X,RU(1,b?{>=0},?c),RL(-1),1,n?) = GG(R(1),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)^(n)*TT(R(-2),X(2),RU,RL(?c),1+b,n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,1,b,?c),X(2,1,1),n)
      +3*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(3,b,?c),X(2,1),n)
      -den(2)^(n)*g(nargs_(?c))*S(R(b+3,?c),X(2),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL,2,n)
      +TT(R,X,RU(1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=-1, p_1=1 and p_2<0 (sommetjes equation 7.172)
id GG(R,X,RU(1,b?{<0},?c),RL(-1),1,n?) = -GG(R(-2),X(2),RU,RL(?c),1+abs_(b),n)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(-1),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,1,b,?c),X(2,1,1),n)
      +3*den(2)*den(2)^(n)*g(nargs_(?c))*S(R(3,b,?c),X(2,1),n)
      -den(2)^(n)*g(nargs_(?c))*S(R(-(abs_(b)+3),?c),X(2),n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL,2,n)
      +TT(R,X,RU(1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=-1, p_1<-1 and p_2>=0 (sommetjes equation 7.173)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(-1),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(-1),RL(?c),1+b,n)
      +TT(R,X,RU(a,b,?c),RL,2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1=-1, p_1<-1 and p_2<0 (sommetjes equation 7.174)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(-1),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL,1,n)*den(2)*den(2)^(n)
      +GG(R(abs_(a)),X(2),RU(-1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-(2+abs_(a)),b,?c),X(2,1),n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,a,b,?c),X(2,1,1),n)
      +TT(R,X,RU(a,b,?c),RL,2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU,RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r=1, q_1=-1, p_1=-1 and p_2>=0 (sommetjes equation 7.175)
id GG(R,X,RU(-1,b?{>=0},?c),RL(-1),1,n?) = -GG(R(-2),X(2),RU,RL(b,?c),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(b,?c),RL,1,n)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,-1,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(-1),RL(?c),1+b,n)
      +TT(R,X,RU(-1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=-1, p_1=-1 and p_2<0 (sommetjes equation 7.176)
id GG(R,X,RU(-1,b?{<0},?c),RL(-1),1,n?) = -GG(R(-2),X(2),RU,RL(b,?c),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(b,?c),RL,1,n)*den(2)^(n)
      +GG(R(1),X(2),RU(-1),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*g(nargs_(?c))*S(R(2,-1,b,?c),X(2,1,1),n)
      +den(2)*den(2)^(n)*g(nargs_(?c))*S(R(-3,b,?c),X(2,1),n)
      +TT(R,X,RU(-1,b,?c),RL,2,n);
**********
* k=1, s>1, r>1, q_1>1 and p_1>1 (sommetjes equation 7.177)
id GG(R,X,RU(a?{>1},b?,?c),RL(d?{>1},e?,?w),1,n?) = GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),1+d,n)
      -sum_(jjj,1,1+d,binom_(-jjj+d+a,-1+a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+a,binom_(-jjj+d+a,-1+d)*GG(R(1-jjj+d+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,a,binom_(-jjj+d+a,d)*GG(R(1-jjj+d+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,d,binom_(-jjj+d+a,a)*GG(R(1-jjj+d+a),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1>1 and p_1=1 (sommetjes equation 7.178)
id GG(R,X,RU(1,b?,?c),RL(d?{>1},e?,?w),1,n?) = -GG(R(1+d),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(1+d),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)*d
      -GG(R(d),X(2),RU(e,?w),RL(b,?c),2,n)*den(2)*den(2)^(n)
      +GG(R(d),X(2),RU(e,?w),RL(1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(1,b,?c),RL(e,?w),1+d,n)
      -sum_(jjj,1,1+d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,d,GG(R(2-jjj+d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.179)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*den(2)*den(2)^(n)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.180)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*den(2)^(n)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*TT(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.181)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*den(2)*den(2)^(n)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),d)*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),d)*den(2)*den(2)^(n)*TT(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.182)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),d)*GG(R(-d-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -binom_(-1+d+abs_(a),d)*GG(R(d+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(d),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*den(2)^(n)*TT(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+d,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(1-jjj+d+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(-1+jjj-d-abs_(a)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.183)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*den(2)^(n)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*d
      -den(2)*den(2)^(n)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*d
      -den(2)*den(2)^(n)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.184)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)*d
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*den(2)^(n)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(-1-d),X(2),RU(b,?c),RL(?w),1+e,n)*d
      -den(2)*den(2)^(n)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.185)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)*d
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*den(2)^(n)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1+d),X(2),RU(e,?w),RL(?c),1+b,n)*d
      -den(2)*den(2)^(n)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.186)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(-1-d),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)*d
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(1+d),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)*d
      +GG(R(d),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*den(2)^(n)*TT(R(d),X(2),RU(e,?w),RL(b,?c),2,n)
      +sum_(jjj,1,d,GG(R(1-jjj+d),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,d,TT(R(-2+jjj-d),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)*d;
* k=1, s>1, r>1, q_1=1 and p_1>1 (sommetjes equation 7.187)
id GG(R,X,RU(a?{>1},b?,?c),RL(1,e?,?w),1,n?) = -GG(R(1+a),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      -GG(R(1+a),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)*a
      -GG(R(a),X(2),RU(b,?c),RL(e,?w),2,n)*den(2)*den(2)^(n)
      +GG(R(a),X(2),RU(b,?c),RL(1,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU(e,?w),RL(b,?c),1+a,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,1,a,GG(R(2-jjj+a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r>1, q_1=1 and p_1=1 (sommetjes equation 7.188)
id GG(R,X,RU(1,b?,?c),RL(1,e?,?w),1,n?) = -GG(R(1),X(2),RU(b,?c),RL(e,?w),2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(1,e,?w),1,n)*den(2)*den(2)^(n)
      -GG(R(1),X(2),RU(e,?w),RL(b,?c),2,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n)
      -GG(R(2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n)
      +GG(R,X,RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.189)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(1,e?{>=0},?w),1,n?) = -abs_(a)*den(2)*den(2)^(n)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -abs_(a)*den(2)*den(2)^(n)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.190)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(1,e?{>=0},?w),1,n?) = -abs_(a)*GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -abs_(a)*den(2)*den(2)^(n)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n)*TT(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.191)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -abs_(a)*den(2)*den(2)^(n)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n)*TT(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.192)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -abs_(a)*GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(1+abs_(a)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(abs_(a)),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(a,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(2-jjj+abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.193)
id GG(R,X,RU(-1,b?{>=0},?c),RL(1,e?{>=0},?w),1,n?) = GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),2,n)
      -den(2)^(n)*TT(R(-2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)^(n)*TT(R(2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(1,e,?w),RL(?c),1+b,n);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.194)
id GG(R,X,RU(-1,b?{<0},?c),RL(1,e?{>=0},?w),1,n?) = GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),2,n)
      -den(2)^(n)*TT(R(-2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.195)
id GG(R,X,RU(-1,b?{>=0},?c),RL(1,e?{<0},?w),1,n?) = -GG(R(-2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),2,n)
      -den(2)^(n)*TT(R(2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(1,e,?w),RL(?c),1+b,n);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.196)
id GG(R,X,RU(-1,b?{<0},?c),RL(1,e?{<0},?w),1,n?) = -GG(R(-2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n)
      +GG(R(1),X(2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n)
      +GG(R,X,RU(-1,b,?c),RL(e,?w),2,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(e,?w),RL(b,?c),2,n);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2>=0 and p_2>=0 (sommetjes equation 7.197)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2>=0 and p_2<0 (sommetjes equation 7.198)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*den(2)^(n)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*TT(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2<0 and p_2>=0 (sommetjes equation 7.199)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*den(2)^(n)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),a)*den(2)*den(2)^(n)*TT(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2<0 and p_2<0 (sommetjes equation 7.200)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),a)*GG(R(-a-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -binom_(-1+a+abs_(d),a)*GG(R(a+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(a),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+a,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(1-jjj+a+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(-1+jjj-a-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2>=0 and p_2>=0 (sommetjes equation 7.201)
id GG(R,X,RU(1,b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*den(2)*den(2)^(n)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -abs_(d)*den(2)*den(2)^(n)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2>=0 and p_2<0 (sommetjes equation 7.202)
id GG(R,X,RU(1,b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -abs_(d)*den(2)*den(2)^(n)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2<0 and p_2>=0 (sommetjes equation 7.203)
id GG(R,X,RU(1,b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -abs_(d)*den(2)*den(2)^(n)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2<0 and p_2<0 (sommetjes equation 7.204)
id GG(R,X,RU(1,b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -abs_(d)*GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(1+abs_(d)),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(abs_(d)),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(d,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(2-jjj+abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.205)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = den(2)*den(2)^(n)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.206)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.207)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.208)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = GG(R(abs_(a)),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(abs_(d)),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*GG(R(-abs_(a)),X(2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*den(2)^(n)*GG(R(-abs_(d)),X(2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(-1+jjj-abs_(a)-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.209)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.210)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.211)
id GG(R,X,RU(-1,b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(d,e,?w),RL(?c),1+b,n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.212)
id GG(R,X,RU(-1,b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(d)),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(abs_(d)),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(d),GG(R(-2+jjj-abs_(d)),X(2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(d),TT(R(1-jjj+abs_(d)),X(2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2>=0 and p_2>=0 (sommetjes equation 7.213)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*a
      -den(2)*den(2)^(n)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*a
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2>=0 and p_2<0 (sommetjes equation 7.214)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)*a
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1+a),X(2),RU(b,?c),RL(?w),1+e,n)*a
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2<0 and p_2>=0 (sommetjes equation 7.215)
id GG(R,X,RU(a?{>1},b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)*a
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(-1-a),X(2),RU(e,?w),RL(?c),1+b,n)*a
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2<0 and p_2<0 (sommetjes equation 7.216)
id GG(R,X,RU(a?{>1},b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      -GG(R(-1-a),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)*a
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(1+a),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)*a
      +GG(R(a),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(a),X(2),RU(b,?c),RL(e,?w),2,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(1-jjj+a),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      -2*sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      -sum_(jjj,2,a,TT(R(-2+jjj-a),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)*a;
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2>=0 and p_2>=0 (sommetjes equation 7.217)
id GG(R,X,RU(1,b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)^(n)*TT(R(-2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)^(n)*TT(R(2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(1,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2>=0 and p_2<0 (sommetjes equation 7.218)
id GG(R,X,RU(1,b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(-2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      -den(2)^(n)*TT(R(2),X(2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(1,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2<0 and p_2>=0 (sommetjes equation 7.219)
id GG(R,X,RU(1,b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n)
      -den(2)^(n)*TT(R(-2),X(2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2<0 and p_2<0 (sommetjes equation 7.220)
id GG(R,X,RU(1,b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(-2),X(2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)^(n)
      +GG(R(1),X(2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      -GG(R(2),X(2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)^(n)
      -den(2)*den(2)^(n)*TT(R(1),X(2),RU(b,?c),RL(e,?w),2,n)
      +TT(R,X,RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.221)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.222)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.223)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.224)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      -GG(R(-1-abs_(a)),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)*den(2)^(n)
      +GG(R(abs_(a)),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +TT(R,X,RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)*den(2)^(n)
      -2*sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n)
      +sum_(jjj,1,abs_(a),GG(R(-2+jjj-abs_(a)),X(2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)*den(2)^(n)
      +sum_(jjj,2,abs_(a),TT(R(1-jjj+abs_(a)),X(2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)*den(2)^(n);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.225)
id GG(R,X,RU(-1,b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.226)
id GG(R,X,RU(-1,b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(-1,b,?c),RL(?w),1+e,n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.227)
id GG(R,X,RU(-1,b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +den(2)*den(2)^(n)*TT(R(1),X(2),RU(-1,e,?w),RL(?c),1+b,n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.228)
id GG(R,X,RU(-1,b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(-2),X(2),RU(b,?c),RL(e,?w),1,n)*den(2)^(n)
      -GG(R(-2),X(2),RU(e,?w),RL(b,?c),1,n)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)*den(2)^(n)
      +GG(R(1),X(2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)*den(2)^(n)
      +TT(R,X,RU(-1,b,?c),RL(e,?w),2,n);
*--#]

*--#]

id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
.sort
*
* The two S-sums recursion 
*
#do i = 1,1

*--#[k>1

*--#[Sign altering
* Case k>1, s=1, p_1>=0 and q_1>=0 (sommetjes equation 7.18)
id TT(R(?e),X(?x),RU(m?{>=0}),RL(c?{>=0},?b),k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?e,m+k-jjj),X(?x,1),RU,RL(c,?b),jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?e,-(m+k-jjj)),X(?x,1),RU(c,?b),RL,jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m),RL(c,?b),jjj,n))
        - binom_(m+k-1,m)*S(R(?e,-(m+k),c,?b),X(?x,1,1),n)*g(nargs_(?b))
        + binom_(m+k-1,m)*S(R(?e,-(m+c+k),?b),X(?x,1),n)*g(nargs_(?b))
        + binom_(m+k-1,m)*TT(R(?e,m+k-1),X(?x,1),RU,RL(?b),c+1,n)
        - TT(R(?e,k-1),X(?x,1),RU(m),RL(?b),c+1,n)
        - TT(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL,m+1,n);
* Case k>1, s=1, p_1>=0 and q_1<0 (sommetjes equation 7.19) 
id TT(R(?e),X(?x),RU(m?{>=0}),RL(c?{<0},?b),k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?e,m+k-jjj),X(?x,1),RU,RL(c,?b),jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?e,-(m+k-jjj)),X(?x,1),RU(c,?b),RL,jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m),RL(c,?b),jjj,n))
        - binom_(m+k-1,m)*S(R(?e,-(m+k),c,?b),X(?x,1,1),n)*g(nargs_(?b))
        + binom_(m+k-1,m)*S(R(?e,m+abs_(c)+k,?b),X(?x,1),n)*g(nargs_(?b))
        + binom_(m+k-1,m)*GG(R(?e,m+k-1),X(?x,1),RU,RL(?b),abs_(c)+1,n)
        - GG(R(?e,k-1),X(?x,1),RU(m),RL(?b),abs_(c)+1,n)
        - TT(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL,m+1,n);
* Case k>1, s>1, p_1>=0, q_1>=0 and p_2>=0 (sommetjes equation 7.20)
id TT(R(?e),X(?x),RU(m?{>=0},d?{>=0},?a),RL(c?{>=0},?b),k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?e,m+k-jjj),X(?x,1),RU(d,?a),RL(c,?b),jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?e,-(m+k-jjj)),X(?x,1),RU(c,?b),RL(d,?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m,d,?a),RL(c,?b),jjj,n))
        + binom_(m+k-1,m)*(TT(R(?e,m+k-1),X(?x,1),RU(d,?a),RL(?b),c+1,n) + TT(R(?e,-(m+k-1)),X(?x,1),RU(c,?b),RL(?a),d+1,n))
        - TT(R(?e,k-1),X(?x,1),RU(m,d,?a),RL(?b),c+1,n)
        - TT(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL(d,?a),m+1,n);
* Case k>1, s>1, p_1>=0, q_1>=0 and p_2<0 (sommetjes equation 7.21) 
id TT(R(?e),X(?x),RU(m?{>=0},d?{<0},?a),RL(c?{>=0},?b),k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?e,m+k-jjj),X(?x,1),RU(d,?a),RL(c,?b),jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?e,-(m+k-jjj)),X(?x,1),RU(c,?b),RL(d,?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m,d,?a),RL(c,?b),jjj,n))
        + binom_(m+k-1,m)*(TT(R(?e,m+k-1),X(?x,1),RU(d,?a),RL(?b),c+1,n) + GG(R(?e,-(m+k-1)),X(?x,1),RU(c,?b),RL(?a),abs_(d)+1,n))
        - TT(R(?e,k-1),X(?x,1),RU(m,d,?a),RL(?b),c+1,n)
        - TT(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL(d,?a),m+1,n);
* Case k>1, s>1, p_1>=0, q_1<0 and p_2>=0 (sommetjes equation 7.22) 
id TT(R(?e),X(?x),RU(m?{>=0},d?{>=0},?a),RL(c?{<0},?b),k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?e,m+k-jjj),X(?x,1),RU(d,?a),RL(c,?b),jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?e,-(m+k-jjj)),X(?x,1),RU(c,?b),RL(d,?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m,d,?a),RL(c,?b),jjj,n))
        + binom_(m+k-1,m)*(GG(R(?e,m+k-1),X(?x,1),RU(d,?a),RL(?b),abs_(c)+1,n) + TT(R(?e,-(m+k-1)),X(?x,1),RU(c,?b),RL(?a),d+1,n))
        - GG(R(?e,k-1),X(?x,1),RU(m,d,?a),RL(?b),abs_(c)+1,n)
        - TT(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL(d,?a),m+1,n);
* Case k>1, s>1, p_1>=0, q_1<0 and p_2<0 (sommetjes equation 7.23) 
id TT(R(?e),X(?x),RU(m?{>=0},d?{<0},?a),RL(c?{<0},?b),k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?e,m+k-jjj),X(?x,1),RU(d,?a),RL(c,?b),jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?e,-(m+k-jjj)),X(?x,1),RU(c,?b),RL(d,?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m,d,?a),RL(c,?b),jjj,n))
        + binom_(m+k-1,m)*(GG(R(?e,m+k-1),X(?x,1),RU(d,?a),RL(?b),abs_(c)+1,n) + GG(R(?e,-(m+k-1)),X(?x,1),RU(c,?b),RL(?a),abs_(d)+1,n))
        - GG(R(?e,k-1),X(?x,1),RU(m,d,?a),RL(?b),abs_(c)+1,n)
        - TT(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL(d,?a),m+1,n);
* Case k>1, s>1, p_1<0 and q_1>=0 (sommetjes equation 7.24) 
id TT(R(?e),X(?x),RU(m?{<0},?a),RL(c?{>=0},?b),k?{>1},n?) = sum_(jjj,1,k,binom_(abs_(m)+k-jjj,abs_(m))*GG(R(?e,-(abs_(m)+k-jjj)),X(?x,1),RU(?a),RL(c,?b),jjj,n))
        + sum_(jjj,1,abs_(m)+1,binom_(abs_(m)+k-jjj,k-1)*GG(R(?e,-(abs_(m)+k-jjj)),X(?x,1),RU(c,?b),RL(?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m,?a),RL(c,?b),jjj,n))
        - TT(R(?e,k-1),X(?x,1),RU(m,?a),RL(?b),c+1,n)
        - GG(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL(?a),abs_(m)+1,n);
* Case k>1, s>1, p_1<0 and q_1<0 (sommetjes equation 7.25) 
id TT(R(?e),X(?x),RU(m?{<0},?a),RL(c?{<0},?b),k?{>1},n?) = sum_(jjj,1,k,binom_(abs_(m)+k-jjj,abs_(m))*GG(R(?e,-(abs_(m)+k-jjj)),X(?x,1),RU(?a),RL(c,?b),jjj,n))
        + sum_(jjj,1,abs_(m)+1,binom_(abs_(m)+k-jjj,k-1)*GG(R(?e,-(abs_(m)+k-jjj)),X(?x,1),RU(c,?b),RL(?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?e,k-jjj),X(?x,1),RU(m,?a),RL(c,?b),jjj,n))
        - GG(R(?e,k-1),X(?x,1),RU(m,?a),RL(?b),abs_(c)+1,n)
        - GG(R(?e,-(k-1)),X(?x,1),RU(c,?b),RL(?a),abs_(m)+1,n);
*--#]

*--#[Fixed sign
* k>1 and p_1>=0 (sommetjes equation 7.98)
id GG(R(?w),X(?y),RU(a?{>=0},?b),RL(c?,?d),k?{>1},n?) = sum_(jjj,1,k,binom_(a+k-jjj,a)*GG(R(?w,a+k-jjj),X(?y,1),RU(?b),RL(c,?d),jjj,n))
        + sum_(jjj,1,a+1,binom_(a+k-jjj,k-1)*GG(R(?w,a+k-jjj),X(?y,1),RU(c,?d),RL(?b),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?w,k-jjj),X(?y,1),RU(a,?b),RL(c,?d),jjj,n))
        - GG(R(?w,k-1),X(?y,1),RU(c,?d),RL(a,?b),1,n);
* k>1, p_1<0, s=1 and q_1>=0 (sommetjes equation 7.99)
id GG(R(?w),X(?y),RU(a?{<0}),RL(c?{>=0},?d),k?{>1},n?) = sum_(jjj,2,k,binom_(abs_(a)+k-jjj,abs_(a))*TT(R(?w,-(abs_(a)+k-jjj)),X(?y,1),RU,RL(c,?d),jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(abs_(a)+k-jjj,k-1)*TT(R(?w,abs_(a)+k-jjj),X(?y,1),RU(c,?d),RL,jjj,n))
        - sum_(jjj,1,k-1,GG(R(?w,k-jjj),X(?y,1),RU(a),RL(c,?d),jjj,n))
        - GG(R(?w,k-1),X(?y,1),RU(c,?d),RL(a),1,n)
        + binom_(abs_(a)+k-1,abs_(a))*TT(R(?w,-(abs_(a)+k-1)),X(?y,1),RU,RL(?d),c+1,n)
        - binom_(abs_(a)+k-1,k-1)*(S(R(?w,abs_(a)+k,c,?d),X(?y,1,1),n)*g(nargs_(?d)) - S(R(?w,abs_(a)+k+c,?d),X(?y,1),n)*g(nargs_(?d)));
* k>1, p_1<0, s=1 and q_1<0 (sommetjes equation 7.100)
id GG(R(?w),X(?y),RU(a?{<0}),RL(c?{<0},?d),k?{>1},n?) = sum_(jjj,2,k,binom_(abs_(a)+k-jjj,abs_(a))*TT(R(?w,-(abs_(a)+k-jjj)),X(?y,1),RU,RL(c,?d),jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(abs_(a)+k-jjj,k-1)*TT(R(?w,abs_(a)+k-jjj),X(?y,1),RU(c,?d),RL,jjj,n))
        - sum_(jjj,1,k-1,GG(R(?w,k-jjj),X(?y,1),RU(a),RL(c,?d),jjj,n))
        - GG(R(?w,k-1),X(?y,1),RU(c,?d),RL(a),1,n)
        + binom_(abs_(a)+k-1,abs_(a))*GG(R(?w,-(abs_(a)+k-1)),X(?y,1),RU,RL(?d),abs_(c)+1,n)
        - binom_(abs_(a)+k-1,k-1)*(S(R(?w,abs_(a)+k,c,?d),X(?y,1,1),n)*g(nargs_(?d)) - S(R(?w,-(abs_(a)+k+abs_(c)),?d),X(?y,1),n)*g(nargs_(?d)));
* k>1, p_1<0, s>1, q_1>=0 and p_2>=0 (sommetjes equation 7.101)
id GG(R(?w),X(?y),RU(a?{<0},b?{>=0},?c),RL(d?{>=0},?e),k?{>1},n?) = sum_(jjj,2,k,binom_(abs_(a)+k-jjj,abs_(a))*TT(R(?w,-(abs_(a)+k-jjj)),X(?y,1),RU(b,?c),RL(d,?e),jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(abs_(a)+k-jjj,k-1)*TT(R(?w,abs_(a)+k-jjj),X(?y,1),RU(d,?e),RL(b,?c),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?w,k-jjj),X(?y,1),RU(a,b,?c),RL(d,?e),jjj,n))
        - GG(R(?w,k-1),X(?y,1),RU(d,?e),RL(a,b,?c),1,n)
        + binom_(abs_(a)+k-1,abs_(a))*TT(R(?w,-(abs_(a)+k-1)),X(?y,1),RU(b,?c),RL(?e),d+1,n)
        + binom_(abs_(a)+k-1,k-1)*TT(R(?w,abs_(a)+k-1),X(?y,1),RU(d,?e),RL(?c),b+1,n);
* k>1, p_1<0, s>1, q_1>=0 and p_2<0 (sommetjes equation 7.102)
id GG(R(?w),X(?y),RU(a?{<0},b?{<0},?c),RL(d?{>=0},?e),k?{>1},n?) = sum_(jjj,2,k,binom_(abs_(a)+k-jjj,abs_(a))*TT(R(?w,-(abs_(a)+k-jjj)),X(?y,1),RU(b,?c),RL(d,?e),jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(abs_(a)+k-jjj,k-1)*TT(R(?w,abs_(a)+k-jjj),X(?y,1),RU(d,?e),RL(b,?c),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?w,k-jjj),X(?y,1),RU(a,b,?c),RL(d,?e),jjj,n))
        - GG(R(?w,k-1),X(?y,1),RU(d,?e),RL(a,b,?c),1,n)
        + binom_(abs_(a)+k-1,abs_(a))*TT(R(?w,-(abs_(a)+k-1)),X(?y,1),RU(b,?c),RL(?e),d+1,n)
        + binom_(abs_(a)+k-1,k-1)*GG(R(?w,abs_(a)+k-1),X(?y,1),RU(d,?e),RL(?c),abs_(b)+1,n);
* k>1, p_1<0, s>1, q_1<0 and p_2>=0 (sommetjes equation 7.103)
id GG(R(?w),X(?y),RU(a?{<0},b?{>=0},?c),RL(d?{<0},?e),k?{>1},n?) = sum_(jjj,2,k,binom_(abs_(a)+k-jjj,abs_(a))*TT(R(?w,-(abs_(a)+k-jjj)),X(?y,1),RU(b,?c),RL(d,?e),jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(abs_(a)+k-jjj,k-1)*TT(R(?w,abs_(a)+k-jjj),X(?y,1),RU(d,?e),RL(b,?c),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?w,k-jjj),X(?y,1),RU(a,b,?c),RL(d,?e),jjj,n))
        - GG(R(?w,k-1),X(?y,1),RU(d,?e),RL(a,b,?c),1,n)
        + binom_(abs_(a)+k-1,abs_(a))*GG(R(?w,-(abs_(a)+k-1)),X(?y,1),RU(b,?c),RL(?e),abs_(d)+1,n)
        + binom_(abs_(a)+k-1,k-1)*TT(R(?w,abs_(a)+k-1),X(?y,1),RU(d,?e),RL(?c),b+1,n);
* k>1, p_1<0, s>1, q_1<0 and p_2<0 (sommetjes equation 7.104)
id GG(R(?w),X(?y),RU(a?{<0},b?{<0},?c),RL(d?{<0},?e),k?{>1},n?) = sum_(jjj,2,k,binom_(abs_(a)+k-jjj,abs_(a))*TT(R(?w,-(abs_(a)+k-jjj)),X(?y,1),RU(b,?c),RL(d,?e),jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(abs_(a)+k-jjj,k-1)*TT(R(?w,abs_(a)+k-jjj),X(?y,1),RU(d,?e),RL(b,?c),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?w,k-jjj),X(?y,1),RU(a,b,?c),RL(d,?e),jjj,n))
        - GG(R(?w,k-1),X(?y,1),RU(d,?e),RL(a,b,?c),1,n)
        + binom_(abs_(a)+k-1,abs_(a))*GG(R(?w,-(abs_(a)+k-1)),X(?y,1),RU(b,?c),RL(?e),abs_(d)+1,n)
        + binom_(abs_(a)+k-1,k-1)*GG(R(?w,abs_(a)+k-1),X(?y,1),RU(d,?e),RL(?c),abs_(b)+1,n);
*--#]

*--#]
.sort
*--#[k=1

*--#[Fixed sign
* k=1, s=1, r=1, q_1>1 and p_1>1 (sommetjes equation 7.105)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(b?{>1}),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU,RL(b),1,n)*den(2)
      +GG(R(?w,y,b),X(?z,m/2,2),RU,RL(a),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL,b,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL,1+b,n)
      +sum_(jjj,1,-1+b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(a),RL,jjj,n))*den(2)
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(b),RL,jjj,n))*den(2)
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU,RL,jjj,n))*den(2);
* k=1, s=1, r=1, q_1>1 and p_1=1 (sommetjes equation 7.106)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(b?{>1}),1,n?) = -GG(R(?w,y,1+b),X(?z,m/2,2),RU,RL,1,n)*den(2)
      -GG(R(?w,y,1+b),X(?z,m/2,2),RU,RL,1,n)*den(2)*b
      +GG(R(?w,y,b),X(?z,m/2,2),RU,RL(1),1,n)*den(2)
      -GG(R(?w,y,b),X(?z,m/2,2),RU,RL,2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(b),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(1),RL,1+b,n)
      -sum_(jjj,1,1+b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(1),RL,jjj,n))*den(2)
      -sum_(jjj,1,b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,1,b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,1,b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL,jjj,n))*den(2)*b;
* k=1, s=1, r=1, q_1>1 and p_1<-1 (sommetjes equation 7.107) 
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(b?{>1}),1,n?) = binom_(-1+b+abs_(a),-1+b)*den(2)*S(R(?w,y,-1-b-abs_(a)),X(?z,m/2,2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*S(R(?w,y,1+b+abs_(a)),X(?z,m/2,2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*S(R(?w,y,-1-b-abs_(a)),X(?z,m/2,2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*S(R(?w,y,1+b+abs_(a)),X(?z,m/2,2),n)
      +GG(R(?w,y,b),X(?z,m/2,2),RU,RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL,1+b,n)
      +den(2)*S(R(?w,y,1+b+abs_(a)),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,1+abs_(a),b),X(?z,m/2,2,1),n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU,RL,1+b,n)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(a),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(?w,y,-1+jjj-b-abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(?w,y,1-jjj+b+abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(?w,y,1-jjj+b+abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(b),RL,jjj,n))*den(2)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(?w,y,-1+jjj-b-abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*den(2);
* k=1, s=1, r=1, q_1>1 and p_1=-1 (sommetjes equation 7.108)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(b?{>1}),1,n?) = GG(R(?w,y,b),X(?z,m/2,2),RU,RL(-1),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1),RL,1+b,n)
      +den(2)*S(R(?w,y,-2-b),X(?z,m/2,2),n)
      +den(2)*S(R(?w,y,-2-b),X(?z,m/2,2),n)*b
      +2*den(2)*S(R(?w,y,2+b),X(?z,m/2,2),n)
      +den(2)*S(R(?w,y,2+b),X(?z,m/2,2),n)*b
      -den(2)*S(R(?w,y,2,b),X(?z,m/2,2,1),n)
      -den(2)*TT(R(?w,y,b),X(?z,m/2,2),RU,RL,2,n)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(-1),RL,jjj,n))*den(2)
      -2*sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL,jjj,n))*den(2)*b;
* k=1, s=1, r=1, q_1=1 and p_1>1 (sommetjes equation 7.109) 
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(1),1,n?) = -GG(R(?w,y,1+a),X(?z,m/2,2),RU,RL,1,n)*den(2)
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU,RL,1,n)*den(2)*a
      +GG(R(?w,y,a),X(?z,m/2,2),RU,RL(1),1,n)*den(2)
      -GG(R(?w,y,a),X(?z,m/2,2),RU,RL,2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL,2,n)
      -sum_(jjj,1,1+a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(1),RL,jjj,n))*den(2)
      -sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)*a;
* k=1, s=1, r=1, q_1=1 and p_1=1 (sommetjes equation 7.110)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(1),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(1),RL,1,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(1),1,n)
      -GG(R(?w,y,1),X(?z,m/2,2),RU,RL,2,n)
      -2*GG(R(?w,y,2),X(?z,m/2,2),RU,RL,1,n)
      +GG(R(?w,y),X(?z,m),RU(1),RL,2,n);
* k=1, s=1, r=1, q_1=1 and p_1<-1 (sommetjes equation 7.111) 
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(1),1,n?) = abs_(a)*den(2)*S(R(?w,y,-2-abs_(a)),X(?z,m/2,2),n)
      +abs_(a)*den(2)*S(R(?w,y,2+abs_(a)),X(?z,m/2,2),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL,2,n)
      +den(2)*S(R(?w,y,-2-abs_(a)),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,1+abs_(a),1),X(?z,m/2,2,1),n)
      +2*den(2)*S(R(?w,y,2+abs_(a)),X(?z,m/2,2),n)
      -sum_(jjj,2,1+abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*abs_(a)*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2);
* k=1, s=1, r=1, q_1=1 and p_1=-1 (sommetjes equation 7.112)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(1),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(-1),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1),RL,2,n)
      +S(R(?w,y,-3),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,2,1),X(?z,m/2,2,1),n)
      +3*den(2)*S(R(?w,y,3),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU,RL,2,n);
* k=1, s=1, r=1, q_1<-1 and p_1>1 (sommetjes equation 7.113) 
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(b?{<-1}),1,n?) = binom_(-1+a+abs_(b),-1+a)*den(2)*S(R(?w,y,-1-a-abs_(b)),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(b),-1+a)*den(2)*S(R(?w,y,1+a+abs_(b)),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*S(R(?w,y,-1-a-abs_(b)),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*S(R(?w,y,1+a+abs_(b)),X(?z,m/2,2),n)
      +GG(R(?w,y,a),X(?z,m/2,2),RU,RL(b),1,n)*den(2)
      +den(2)*S(R(?w,y,1+a+abs_(b)),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,1+abs_(b),a),X(?z,m/2,2,1),n)
      +den(2)*TT(R(?w,y,-abs_(b)),X(?z,m/2,2),RU,RL,1+a,n)
      +TT(R(?w,y),X(?z,m),RU(a),RL,1+abs_(b),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(b),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(?w,y,-1+jjj-a-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(?w,y,1-jjj+a+abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(?w,y,1-jjj+a+abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(a),RL,jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(?w,y,-1+jjj-a-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2);
* k=1, s=1, r=1, q_1<-1 and p_1=1 (sommetjes equation 7.114)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(b?{<-1}),1,n?) = abs_(b)*den(2)*S(R(?w,y,-2-abs_(b)),X(?z,m/2,2),n)
      +abs_(b)*den(2)*S(R(?w,y,2+abs_(b)),X(?z,m/2,2),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(b),1,n)*den(2)
      +den(2)*S(R(?w,y,-2-abs_(b)),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,1+abs_(b),1),X(?z,m/2,2,1),n)
      +2*den(2)*S(R(?w,y,2+abs_(b)),X(?z,m/2,2),n)
      +TT(R(?w,y),X(?z,m),RU(1),RL,1+abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(1),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*abs_(b)*den(2)
      -sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2);
* k=1, s=1, r=1, q_1<-1 and p_1<-1 (sommetjes equation 7.115) 
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(b?{<-1}),1,n?) = GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU,RL,1+abs_(b),n)*den(2)
      +GG(R(?w,y,-abs_(b)),X(?z,m/2,2),RU,RL,1+abs_(a),n)*den(2)
      +2*den(2)*S(R(?w,y,-1-abs_(a)-abs_(b)),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,1+abs_(a),b),X(?z,m/2,2,1),n)
      -den(2)*S(R(?w,y,1+abs_(b),a),X(?z,m/2,2,1),n)
      +TT(R(?w,y),X(?z,m),RU(a),RL,1+abs_(b),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(a),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(b),RL,jjj,n))*den(2);
* k=1, s=1, r=1, q_1<-1 and p_1=-1 (sommetjes equation 7.116)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(b?{<-1}),1,n?) = -abs_(b)*GG(R(?w,y,-1-abs_(b)),X(?z,m/2,2),RU,RL,1,n)*den(2)
      -GG(R(?w,y,-1-abs_(b)),X(?z,m/2,2),RU,RL,1,n)*den(2)
      +S(R(?w,y,-2-abs_(b)),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,1+abs_(b),-1),X(?z,m/2,2,1),n)
      -den(2)*S(R(?w,y,2,b),X(?z,m/2,2,1),n)
      +TT(R(?w,y),X(?z,m),RU(-1),RL,abs_(b)+1,n)
      -sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*abs_(b)*den(2)
      -2*sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(-1),RL,jjj,n))*den(2);
* k=1, s=1, r=1, q_1=-1 and p_1>1 (sommetjes equation 7.117) 
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(-1),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU,RL(-1),1,n)*den(2)
      +den(2)*S(R(?w,y,-2-a),X(?z,m/2,2),n)
      +den(2)*S(R(?w,y,-2-a),X(?z,m/2,2),n)*a
      +2*den(2)*S(R(?w,y,2+a),X(?z,m/2,2),n)
      +den(2)*S(R(?w,y,2+a),X(?z,m/2,2),n)*a
      -den(2)*S(R(?w,y,2,a),X(?z,m/2,2,1),n)
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU,RL,2,n)
      +TT(R(?w,y),X(?z,m),RU(a),RL,2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1),RL,jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL,jjj,n))*den(2)*a;
* k=1, s=1, r=1, q_1=-1 and p_1=1 (sommetjes equation 7.118)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(-1),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(-1),1,n)*den(2)
      +2*den(2)*S(R(?w,y,-3),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,2,1),X(?z,m/2,2,1),n)
      +3*den(2)*S(R(?w,y,3),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU,RL,2,n)
      +TT(R(?w,y),X(?z,m),RU(1),RL,2,n);
* k=1, s=1, r=1, q_1=-1 and p_1<-1 (sommetjes equation 7.119) 
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(-1),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL,1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL,1,n)*den(2)
      +S(R(?w,y,-2-abs_(a)),X(?z,m/2,2),n)
      -den(2)*S(R(?w,y,1+abs_(a),-1),X(?z,m/2,2,1),n)
      -den(2)*S(R(?w,y,2,a),X(?z,m/2,2,1),n)
      +TT(R(?w,y),X(?z,m),RU(a),RL,2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL,jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL,jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1),RL,jjj,n))*den(2);
* k=1, s=1, r=1, q_1=-1 and p_1=-1 (sommetjes equation 7.120)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(-1),1,n?) = -2*GG(R(?w,y,-2),X(?z,m/2,2),RU,RL,1,n)
      -S(R(?w,y,2,-1),X(?z,m/2,2,1),n)
      +S(R(?w,y,-3),X(?z,m/2,2),n)
      +TT(R(?w,y),X(?z,m),RU(-1),RL,2,n);
*********
* k=1, s=1, r>1, q_1>1 and p_1>1 (sommetjes equation 7.121) 
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(b?{>1},c?,?d),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU,RL(b,c,?d),1,n)*den(2)
      +GG(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL(c,?d),1+b,n)
      -sum_(jjj,1,1+b,binom_(-jjj+b+a,-1+a)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,1,1+a,binom_(-jjj+b+a,-1+b)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,1,a,binom_(-jjj+b+a,b)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(b,c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,1,b,binom_(-jjj+b+a,a)*GG(R(?w,y,1-jjj+b+a),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(a),RL(c,?d),jjj,n))*den(2);
* k=1, s=1, r>1, q_1>1 and p_1=1 (sommetjes equation 7.122)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(b?{>1},c?,?d),1,n?) = -GG(R(?w,y,1+b),X(?z,m/2,2),RU(c,?d),RL,1,n)*den(2)
      -GG(R(?w,y,1+b),X(?z,m/2,2),RU(c,?d),RL,1,n)*den(2)*b
      +GG(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL(1),1,n)*den(2)
      -GG(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL,2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,c,?d),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(b,c,?d),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(1),RL(c,?d),1+b,n)
      -sum_(jjj,1,1+b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(1),RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,1,b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,1,b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL(c,?d),jjj,n)*jjj)*den(2)
      -sum_(jjj,1,b,GG(R(?w,y,2-jjj+b),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)*b;
* k=1, s=1, r>1, q_1>1, p_1<-1 and q_2>=0 (sommetjes equation 7.123)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(b?{>1},c?{>=0},?d),1,n?) = -binom_(-1+b+abs_(a),-1+b)*den(2)*g(nargs_(?d))*S(R(?w,y,1+c+b+abs_(a),?d),X(?z,m/2,2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*g(nargs_(?d))*S(R(?w,y,1+b+abs_(a),c,?d),X(?z,m/2,2,1),n)
      -binom_(-1+b+abs_(a),abs_(a))*den(2)*TT(R(?w,y,-b-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      -binom_(-1+b+abs_(a),b)*den(2)*g(nargs_(?d))*S(R(?w,y,1+c+b+abs_(a),?d),X(?z,m/2,2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*g(nargs_(?d))*S(R(?w,y,1+b+abs_(a),c,?d),X(?z,m/2,2,1),n)
      -binom_(-1+b+abs_(a),b)*den(2)*TT(R(?w,y,-b-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      +GG(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL(c,?d),1+b,n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,1+b+abs_(a),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),b,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1+b,n)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(a),RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(?w,y,-1+jjj-b-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(?w,y,1-jjj+b+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(?w,y,1-jjj+b+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(b,c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(?w,y,-1+jjj-b-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2);
* k=1, s=1, r>1, q_1>1, p_1<-1 and q_2<0 (sommetjes equation 7.124)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(b?{>1},c?{<0},?d),1,n?) = -binom_(-1+b+abs_(a),-1+b)*den(2)*g(nargs_(?d))*S(R(?w,y,-1-b-abs_(a)-abs_(c),?d),X(?z,m/2,2),n)
      +binom_(-1+b+abs_(a),-1+b)*den(2)*g(nargs_(?d))*S(R(?w,y,1+b+abs_(a),c,?d),X(?z,m/2,2,1),n)
      -binom_(-1+b+abs_(a),abs_(a))*GG(R(?w,y,-b-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      -binom_(-1+b+abs_(a),b)*GG(R(?w,y,-b-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      -binom_(-1+b+abs_(a),b)*den(2)*g(nargs_(?d))*S(R(?w,y,-1-b-abs_(a)-abs_(c),?d),X(?z,m/2,2),n)
      +binom_(-1+b+abs_(a),b)*den(2)*g(nargs_(?d))*S(R(?w,y,1+b+abs_(a),c,?d),X(?z,m/2,2,1),n)
      +GG(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL(c,?d),1+b,n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,1+b+abs_(a),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),b,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1+b,n)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(a),RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,1+b,binom_(-jjj+b+abs_(a),-1+abs_(a))*TT(R(?w,y,-1+jjj-b-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+b+abs_(a),-1+b)*TT(R(?w,y,1-jjj+b+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),binom_(-jjj+b+abs_(a),b)*TT(R(?w,y,1-jjj+b+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(b,c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,b,binom_(-jjj+b+abs_(a),abs_(a))*TT(R(?w,y,-1+jjj-b-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2);
* k=1, s=1, r>1, q_1>1, p_1=-1 and q_2>=0 (sommetjes equation 7.125)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(b?{>1},c?{>=0},?d),1,n?) = GG(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL(-1),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1),RL(c,?d),1+b,n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2+c+b,?d),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2+c+b,?d),X(?z,m/2,2),n)*b
      +2*den(2)*g(nargs_(?d))*S(R(?w,y,2+b,c,?d),X(?z,m/2,2,1),n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,2+b,c,?d),X(?z,m/2,2,1),n)*b
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,b,c,?d),X(?z,m/2,2,1,1),n)
      -den(2)*TT(R(?w,y,-1-b),X(?z,m/2,2),RU,RL(?d),1+c,n)
      -den(2)*TT(R(?w,y,-1-b),X(?z,m/2,2),RU,RL(?d),1+c,n)*b
      -den(2)*TT(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL,2,n)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(-1),RL(c,?d),jjj,n))*den(2)
      -2*sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL(c,?d),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)*b;
* k=1, s=1, r>1, q_1>1, p_1=-1 and q_2<0 (sommetjes equation 7.126)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(b?{>1},c?{<0},?d),1,n?) = -GG(R(?w,y,-1-b),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      -GG(R(?w,y,-1-b),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)*b
      +GG(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL(-1),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1),RL(c,?d),1+b,n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,-2-b-abs_(c),?d),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,-2-b-abs_(c),?d),X(?z,m/2,2),n)*b
      +2*den(2)*g(nargs_(?d))*S(R(?w,y,2+b,c,?d),X(?z,m/2,2,1),n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,2+b,c,?d),X(?z,m/2,2,1),n)*b
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,b,c,?d),X(?z,m/2,2,1,1),n)
      -den(2)*TT(R(?w,y,b),X(?z,m/2,2),RU(c,?d),RL,2,n)
      +sum_(jjj,1,b,GG(R(?w,y,1-jjj+b),X(?z,m/2,2),RU(-1),RL(c,?d),jjj,n))*den(2)
      -2*sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL(c,?d),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,b,TT(R(?w,y,-2+jjj-b),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)*b;
* k=1, s=1, r>1, q_1=1 and p_1>1 (sommetjes equation 7.127)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(1,c?,?d),1,n?) = -GG(R(?w,y,1+a),X(?z,m/2,2),RU,RL(c,?d),1,n)*den(2)
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU,RL(c,?d),1,n)*den(2)*a
      -GG(R(?w,y,a),X(?z,m/2,2),RU,RL(c,?d),2,n)*den(2)
      +GG(R(?w,y,a),X(?z,m/2,2),RU,RL(1,c,?d),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL(c,?d),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL(a),1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL,1+a,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL(c,?d),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(1,c,?d),RL,jjj,n))*den(2)
      -2*sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU(c,?d),RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)*a;
* k=1, s=1, r>1, q_1=1 and p_1=1 (sommetjes equation 7.128)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(1,c?,?d),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL(1),1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL,2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1),RL(c,?d),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,c,?d),RL,1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU,RL(c,?d),2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(1,c,?d),1,n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(c,?d),RL,1,n)
      -GG(R(?w,y,2),X(?z,m/2,2),RU,RL(c,?d),1,n)
      +GG(R(?w,y),X(?z,m),RU(1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=1, p_1<-1 and q_2>=0 (sommetjes equation 7.129)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(1,c?{>=0},?d),1,n?) = -abs_(a)*den(2)*g(nargs_(?d))*S(R(?w,y,2+c+abs_(a),?d),X(?z,m/2,2),n)
      +(abs_(a)+2)*den(2)*g(nargs_(?d))*S(R(?w,y,2+abs_(a),c,?d),X(?z,m/2,2,1),n)
      -abs_(a)*den(2)*TT(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL(c,?d),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL(c,?d),2,n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),1,c,?d),X(?z,m/2,2,1,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2+c+abs_(a),?d),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL,1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1,c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n)*jjj)*den(2);
* k=1, s=1, r>1, q_1=1, p_1<-1 and q_2<0 (sommetjes equation 7.130)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(1,c?{<0},?d),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      -abs_(a)*den(2)*g(nargs_(?d))*S(R(?w,y,-2-abs_(a)-abs_(c),?d),X(?z,m/2,2),n)
      +(abs_(a)+2)*den(2)*g(nargs_(?d))*S(R(?w,y,2+abs_(a),c,?d),X(?z,m/2,2,1),n)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL(c,?d),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL(a),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a),RL(c,?d),2,n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,-2-abs_(a)-abs_(c),?d),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),1,c,?d),X(?z,m/2,2,1,1),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL,1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1,c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n)*jjj)*den(2);
* k=1, s=1, r>1, q_1=1, p_1=-1 and q_2>=0 (sommetjes equation 7.131)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(1,c?{>=0},?d),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL(-1),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(c,?d),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1),RL(c,?d),2,n)
      -TT(R(?w,y,-2),X(?z,m/2,2),RU,RL(?d),1+c,n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,1,c,?d),X(?z,m/2,2,1,1),n)
      +3*den(2)*g(nargs_(?d))*S(R(?w,y,3,c,?d),X(?z,m/2,2,1),n)
      -2*den(2)*g(nargs_(?d))*S(R(?w,y,c+3,?d),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL,2,n);
* k=1, s=1, r>1, q_1=1, p_1=-1 and q_2<0 (sommetjes equation 7.132)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(1,c?{<0},?d),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL(-1),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(c,?d),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1),RL(c,?d),2,n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,1,c,?d),X(?z,m/2,2,1,1),n)
      +3*den(2)*g(nargs_(?d))*S(R(?w,y,3,c,?d),X(?z,m/2,2,1),n)
      -2*den(2)*g(nargs_(?d))*S(R(?w,y,-(abs_(c)+3),?d),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(c,?d),RL,2,n);
* k=1, s=1, r>1, q_1<-1, p_1>1 and q_2>=0 (sommetjes equation 7.133)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(b?{<-1},c?{>=0},?d),1,n?) = -binom_(-1+a+abs_(b),abs_(b))*den(2)*g(nargs_(?d))*S(R(?w,y,-1-c-a-abs_(b),?d),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*g(nargs_(?d))*S(R(?w,y,-1-a-abs_(b),c,?d),X(?z,m/2,2,1),n)
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*TT(R(?w,y,a+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      -binom_(-1+a+abs_(b),a)*den(2)*g(nargs_(?d))*S(R(?w,y,-(1+c+a+abs_(b)),?d),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*g(nargs_(?d))*S(R(?w,y,-(1+a+abs_(b)),c,?d),X(?z,m/2,2,1),n)
      -binom_(-1+a+abs_(b),a)*den(2)*TT(R(?w,y,a+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      +GG(R(?w,y,a),X(?z,m/2,2),RU,RL(b,c,?d),1,n)*den(2)
      +den(2)*TT(R(?w,y,-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1+a,n)
      +den(2)*TT(R(?w,y,abs_(b)),X(?z,m/2,2),RU(a),RL(?d),1+c,n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),1+abs_(b),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(b,c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(?w,y,-1+jjj-a-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(?w,y,1-jjj+a+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(?w,y,1-jjj+a+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(a),RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(?w,y,-1+jjj-a-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2);
* k=1, s=1, r>1, q_1<-1, p_1>1 and q_2<0 (sommetjes equation 7.134)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(b?{<-1},c?{<0},?d),1,n?) = -binom_(-1+a+abs_(b),abs_(b))*GG(R(?w,y,a+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      +binom_(-1+a+abs_(b),abs_(b))*den(2)*g(nargs_(?d))*S(R(?w,y,-1-a-abs_(b),c,?d),X(?z,m/2,2,1),n)
      -binom_(-1+a+abs_(b),abs_(b))*den(2)*g(nargs_(?d))*S(R(?w,y,1+a+abs_(b)+abs_(c),?d),X(?z,m/2,2),n)
      -binom_(-1+a+abs_(b),a)*GG(R(?w,y,a+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      -binom_(-1+a+abs_(b),a)*den(2)*g(nargs_(?d))*S(R(?w,y,-(-1-a-abs_(b)-abs_(c)),?d),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(b),a)*den(2)*g(nargs_(?d))*S(R(?w,y,-(1+a+abs_(b)),c,?d),X(?z,m/2,2,1),n)
      +GG(R(?w,y,abs_(b)),X(?z,m/2,2),RU(a),RL(?d),1+abs_(c),n)*den(2)
      +GG(R(?w,y,a),X(?z,m/2,2),RU,RL(b,c,?d),1,n)*den(2)
      +den(2)*TT(R(?w,y,-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1+a,n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),1+abs_(b),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(b,c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(b),-1+abs_(b))*TT(R(?w,y,-1+jjj-a-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(b),binom_(-jjj+a+abs_(b),-1+a)*TT(R(?w,y,1-jjj+a+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,abs_(b),binom_(-jjj+a+abs_(b),a)*TT(R(?w,y,1-jjj+a+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(a),RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(b),abs_(b))*TT(R(?w,y,-1+jjj-a-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2);
* k=1, s=1, r>1, q_1<-1, p_1=1 and q_2>=0 (sommetjes equation 7.135)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(b?{<-1},c?{>=0},?d),1,n?) = -(abs_(b)+1)*den(2)*g(nargs_(?d))*S(R(?w,y,-(2+c+abs_(b)),?d),X(?z,m/2,2),n)
      +(abs_(b)+1)*den(2)*g(nargs_(?d))*S(R(?w,y,-(2+abs_(b)),c,?d),X(?z,m/2,2,1),n)
      -abs_(b)*den(2)*TT(R(?w,y,1+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,c,?d),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(b,c,?d),1,n)*den(2)
      -den(2)*TT(R(?w,y,1+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+c,n)
      +den(2)*TT(R(?w,y,abs_(b)),X(?z,m/2,2),RU(1),RL(?d),1+c,n)
      +TT(R(?w,y),X(?z,m),RU(1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(1),RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)
      -sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n)*jjj)*den(2);
* k=1, s=1, r>1, q_1<-1, p_1=1 and q_2<0 (sommetjes equation 7.136)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(b?{<-1},c?{<0},?d),1,n?) = -abs_(b)*GG(R(?w,y,1+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      -(abs_(b)+1)*den(2)*g(nargs_(?d))*S(R(?w,y,-(-2-abs_(b)-abs_(c)),?d),X(?z,m/2,2),n)
      +(abs_(b)+1)*den(2)*g(nargs_(?d))*S(R(?w,y,-(2+abs_(b)),c,?d),X(?z,m/2,2,1),n)
      -GG(R(?w,y,1+abs_(b)),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      +GG(R(?w,y,abs_(b)),X(?z,m/2,2),RU(1),RL(?d),1+abs_(c),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,c,?d),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(b,c,?d),1,n)*den(2)
      +TT(R(?w,y),X(?z,m),RU(1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,2,1+abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(1),RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)
      -sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,2-jjj+abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n)*jjj)*den(2);
* k=1, s=1, r>1, q_1<-1, p_1<-1 and q_2>=0 (sommetjes equation 7.137)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(b?{<-1},c?{>=0},?d),1,n?) = GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1+abs_(b),n)*den(2)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-1-abs_(a)-abs_(b),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),b,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*GG(R(?w,y,-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1+abs_(a),n)
      +den(2)*TT(R(?w,y,abs_(b)),X(?z,m/2,2),RU(a),RL(?d),1+c,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(a),RL(c,?d),abs_(b),n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,c,?d),RL,abs_(a),n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,-1+abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(b,c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,-1+abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(a),RL(c,?d),jjj,n))*den(2);
* k=1, s=1, r>1, q_1<-1, p_1<-1 and q_2<0 (sommetjes equation 7.138)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(b?{<-1},c?{<0},?d),1,n?) = GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1+abs_(b),n)*den(2)
      +GG(R(?w,y,abs_(b)),X(?z,m/2,2),RU(a),RL(?d),1+abs_(c),n)*den(2)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-1-abs_(a)-abs_(b),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),b,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*GG(R(?w,y,-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1+abs_(a),n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(b))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(b),binom_(-jjj+abs_(a)+abs_(b),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(b),abs_(b))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      -sum_(jjj,1,abs_(b),binom_(-jjj+abs_(a)+abs_(b),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(b,c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(a),RL(c,?d),jjj,n))*den(2);
* k=1, s=1, r>1, q_1<-1, p_1=-1 and q_2>=0 (sommetjes equation 7.139)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(b?{<-1},c?{>=0},?d),1,n?) = -abs_(b)*GG(R(?w,y,-1-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1,n)*den(2)
      -GG(R(?w,y,-1-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1,n)*den(2)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-(2+abs_(b)),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,b,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,abs_(b)),X(?z,m/2,2),RU(-1),RL(?d),1+c,n)
      +TT(R(?w,y),X(?z,m),RU(-1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)
      -2*sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(-1),RL(c,?d),jjj,n))*den(2);
* k=1, s=1, r>1, q_1<-1, p_1=-1 and q_2<0 (sommetjes equation 7.140)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(b?{<-1},c?{<0},?d),1,n?) = -abs_(b)*GG(R(?w,y,-1-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1,n)*den(2)
      -GG(R(?w,y,-1-abs_(b)),X(?z,m/2,2),RU(c,?d),RL,1,n)*den(2)
      +GG(R(?w,y,abs_(b)),X(?z,m/2,2),RU(-1),RL(?d),1+abs_(c),n)*den(2)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-(2+abs_(b)),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,b,c,?d),X(?z,m/2,2,1,1),n)
      +TT(R(?w,y),X(?z,m),RU(-1),RL(c,?d),1+abs_(b),n)
      -sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*abs_(b)*den(2)
      -2*sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n))*den(2)
      +sum_(jjj,1,abs_(b),GG(R(?w,y,-2+jjj-abs_(b)),X(?z,m/2,2),RU,RL(c,?d),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(b),TT(R(?w,y,1-jjj+abs_(b)),X(?z,m/2,2),RU(-1),RL(c,?d),jjj,n))*den(2);
* k=1, s=1, r>1, q_1=-1, p_1>1 and q_2>=0 (sommetjes equation 7.141)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(-1,c?{>=0},?d),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU,RL(-1,c,?d),1,n)*den(2)
      -den(2)*g(nargs_(?d))*S(R(?w,y,-2-c-a,?d),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,-2-c-a,?d),X(?z,m/2,2),n)*a
      +den(2)*g(nargs_(?d))*S(R(?w,y,-2-a,c,?d),X(?z,m/2,2,1),n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-2-a,c,?d),X(?z,m/2,2,1),n)*a
      -den(2)*TT(R(?w,y,1+a),X(?z,m/2,2),RU,RL(?d),1+c,n)
      -den(2)*TT(R(?w,y,1+a),X(?z,m/2,2),RU,RL(?d),1+c,n)*a
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU,RL(c,?d),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(a),RL(?d),1+c,n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1,c,?d),RL,jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(c,?d),RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)*a;
* k=1, s=1, r>1, q_1=-1, p_1>1 and q_2<0 (sommetjes equation 7.142)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1}),RL(-1,c?{<0},?d),1,n?) = -GG(R(?w,y,1+a),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)*den(2)*a
      +GG(R(?w,y,a),X(?z,m/2,2),RU,RL(-1,c,?d),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL(?d),1+abs_(c),n)*den(2)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-2-a,c,?d),X(?z,m/2,2,1),n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-2-a,c,?d),X(?z,m/2,2,1),n)*a
      -den(2)*g(nargs_(?d))*S(R(?w,y,2+a+abs_(c),?d),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2+a+abs_(c),?d),X(?z,m/2,2),n)*a
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU,RL(c,?d),2,n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1,c,?d),RL,jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(c,?d),RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)*a;
* k=1, s=1, r>1, q_1=-1, p_1=1 and q_2>=0 (sommetjes equation 7.143)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(-1,c?{>=0},?d),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(-1,c,?d),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(-1,c,?d),1,n)*den(2)
      -g(nargs_(?d))*S(R(?w,y,-3-c,?d),X(?z,m/2,2),n)
      +g(nargs_(?d))*S(R(?w,y,-3,c,?d),X(?z,m/2,2,1),n)
      -TT(R(?w,y,2),X(?z,m/2,2),RU,RL(?d),1+c,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(1),RL(?d),1+c,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU,RL(c,?d),2,n)
      +TT(R(?w,y),X(?z,m),RU(1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=-1, p_1=1 and q_2<0 (sommetjes equation 7.144)
id GG(R(?w,y?),X(?z,m?),RU(1),RL(-1,c?{<0},?d),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(-1,c,?d),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1),RL(?d),1+abs_(c),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(-1,c,?d),1,n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU,RL(?d),1+abs_(c),n)
      -g(nargs_(?d))*S(R(?w,y,3+abs_(c),?d),X(?z,m/2,2),n)
      +g(nargs_(?d))*S(R(?w,y,-3,c,?d),X(?z,m/2,2,1),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU,RL(c,?d),2,n)
      +TT(R(?w,y),X(?z,m),RU(1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=-1, p_1<-1 and q_2>=0 (sommetjes equation 7.145)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(-1,c?{>=0},?d),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1,n)*den(2)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-2-abs_(a),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),-1,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(a),RL(?d),1+c,n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1,c,?d),RL,jjj,n))*den(2);
* k=1, s=1, r>1, q_1=-1, p_1<-1 and q_2<0 (sommetjes equation 7.146)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1}),RL(-1,c?{<0},?d),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU,RL(c,?d),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a),RL(?d),1+abs_(c),n)*den(2)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-2-abs_(a),c,?d),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,1+abs_(a),-1,c,?d),X(?z,m/2,2,1,1),n)
      +TT(R(?w,y),X(?z,m),RU(a),RL(c,?d),2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(c,?d),RL,jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1,c,?d),RL,jjj,n))*den(2);
* k=1, s=1, r>1, q_1=-1, p_1=-1 and q_2>=0 (sommetjes equation 7.147)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(-1,c?{>=0},?d),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU,RL(c,?d),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(c,?d),RL,1,n)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,-1,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-3,c,?d),X(?z,m/2,2,1),n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(?d),1+c,n)
      +TT(R(?w,y),X(?z,m),RU(-1),RL(c,?d),2,n);
* k=1, s=1, r>1, q_1=-1, p_1=-1 and q_2<0 (sommetjes equation 7.148)
id GG(R(?w,y?),X(?z,m?),RU(-1),RL(-1,c?{<0},?d),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU,RL(c,?d),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(c,?d),RL,1,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(?d),1+abs_(c),n)*den(2)
      -den(2)*g(nargs_(?d))*S(R(?w,y,2,-1,c,?d),X(?z,m/2,2,1,1),n)
      +den(2)*g(nargs_(?d))*S(R(?w,y,-3,c,?d),X(?z,m/2,2,1),n)
      +TT(R(?w,y),X(?z,m),RU(-1),RL(c,?d),2,n);
**********
* k=1, s>1, r=1, q_1>1 and p_1>1 (sommetjes equation 7.149) 
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?,?c),RL(d?{>1}),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d),1,n)*den(2)
      +GG(R(?w,y,d),X(?z,m/2,2),RU,RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d),RL(b,?c),a,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL,d,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL,1+d,n)
      +sum_(jjj,1,-1+d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,1,-1+a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,1+d,GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+a,-1+a))*den(2)
      -sum_(jjj,1,1+a,GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+a,-1+d))*den(2)
      -sum_(jjj,1,a,GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+a,d))*den(2)
      -sum_(jjj,1,d,GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+a,a))*den(2);
* k=1, s>1, r=1, q_1>1 and p_1=1 (sommetjes equation 7.150)
id GG(R(?w,y?),X(?z,m?),RU(1,b?,?c),RL(d?{>1}),1,n?) = -GG(R(?w,y,1+d),X(?z,m/2,2),RU,RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,1+d),X(?z,m/2,2),RU,RL(b,?c),1,n)*den(2)*d
      -GG(R(?w,y,d),X(?z,m/2,2),RU,RL(b,?c),2,n)*den(2)
      +GG(R(?w,y,d),X(?z,m/2,2),RU,RL(1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d),1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL,1+d,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(1,b,?c),RL,1+d,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(1,b,?c),RL,jjj,n))*den(2)
      -2*sum_(jjj,1,d,GG(R(?w,y,2-jjj+d),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,1,d,GG(R(?w,y,2-jjj+d),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,1,d,GG(R(?w,y,2-jjj+d),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)*d;
* k=1, s>1, r=1, q_1>1, p_1<-1 and p_2>=0 (sommetjes equation 7.151)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(d?{>1}),1,n?) = -binom_(-1+d+abs_(a),abs_(a))*den(2)*S(R(?w,y,-1-d-b-abs_(a),?c),X(?z,m/2,2),n)*g(nargs_(?c))
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*S(R(?w,y,-1-d-abs_(a),b,?c),X(?z,m/2,2,1),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*TT(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),d)*den(2)*S(R(?w,y,-(1+d+b+abs_(a)),?c),X(?z,m/2,2),n)*g(nargs_(?c))
      +binom_(-1+d+abs_(a),d)*den(2)*S(R(?w,y,-(1+d+abs_(a)),b,?c),X(?z,m/2,2,1),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),d)*den(2)*TT(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      +GG(R(?w,y,d),X(?z,m/2,2),RU,RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL,1+d,n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1+d,n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+d,TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),-1+abs_(a)))*den(2)
      -sum_(jjj,2,1+abs_(a),TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),-1+d))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),d))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),abs_(a)))*den(2);
* k=1, s>1, r=1, q_1>1, p_1<-1 and p_2<0 (sommetjes equation 7.152)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(d?{>1}),1,n?) = -binom_(-1+d+abs_(a),abs_(a))*GG(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      +binom_(-1+d+abs_(a),abs_(a))*den(2)*S(R(?w,y,-1-d-abs_(a),b,?c),X(?z,m/2,2,1),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*S(R(?w,y,1+d+abs_(a)+abs_(b),?c),X(?z,m/2,2),n)*g(nargs_(?c))
      -binom_(-1+d+abs_(a),d)*GG(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+d+abs_(a),d)*den(2)*S(R(?w,y,-(-1-d-abs_(a)-abs_(b)),?c),X(?z,m/2,2),n)*g(nargs_(?c))
      +binom_(-1+d+abs_(a),d)*den(2)*S(R(?w,y,-(1+d+abs_(a)),b,?c),X(?z,m/2,2,1),n)*g(nargs_(?c))
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,d),X(?z,m/2,2),RU,RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL,1+d,n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1+d,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,1+d,TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),-1+abs_(a)))*den(2)
      -sum_(jjj,2,1+abs_(a),TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),-1+d))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*binom_(-jjj+d+abs_(a),d))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*binom_(-jjj+d+abs_(a),abs_(a)))*den(2);
* k=1, s>1, r=1, q_1>1, p_1=-1 and p_2>=0 (sommetjes equation 7.153)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(d?{>1}),1,n?) = GG(R(?w,y,d),X(?z,m/2,2),RU,RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL,1+d,n)
      +den(2)*S(R(?w,y,-2-d,b,?c),X(?z,m/2,2,1),n)*g(nargs_(?c))
      +den(2)*S(R(?w,y,-2-d,b,?c),X(?z,m/2,2,1),n)*d*g(nargs_(?c))
      -den(2)*S(R(?w,y,-2-d-b,?c),X(?z,m/2,2),n)*g(nargs_(?c))
      -den(2)*S(R(?w,y,-2-d-b,?c),X(?z,m/2,2),n)*d*g(nargs_(?c))
      -den(2)*TT(R(?w,y,1+d),X(?z,m/2,2),RU,RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1+d),X(?z,m/2,2),RU,RL(?c),1+b,n)*d
      -den(2)*TT(R(?w,y,d),X(?z,m/2,2),RU,RL(b,?c),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(d),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(-1,b,?c),RL,jjj,n))*den(2)
      -2*sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)*d;
* k=1, s>1, r=1, q_1>1, p_1=-1 and p_2<0 (sommetjes equation 7.154)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(d?{>1}),1,n?) = -GG(R(?w,y,1+d),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,1+d),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)*d
      +GG(R(?w,y,d),X(?z,m/2,2),RU,RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL,1+d,n)
      +den(2)*S(R(?w,y,-2-d,b,?c),X(?z,m/2,2,1),n)*g(nargs_(?c))
      +den(2)*S(R(?w,y,-2-d,b,?c),X(?z,m/2,2,1),n)*d*g(nargs_(?c))
      -den(2)*S(R(?w,y,2+d+abs_(b),?c),X(?z,m/2,2),n)*g(nargs_(?c))
      -den(2)*S(R(?w,y,2+d+abs_(b),?c),X(?z,m/2,2),n)*d*g(nargs_(?c))
      -den(2)*TT(R(?w,y,d),X(?z,m/2,2),RU,RL(b,?c),2,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(-1,b,?c),RL,jjj,n))*den(2)
      -2*sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*jjj)*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)*d;
* k=1, s>1, r=1, q_1=1 and p_1>1 (sommetjes equation 7.155)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?,?c),RL(1),1,n?) = -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL,1,n)*den(2)
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL,1,n)*den(2)*a
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(1),1,n)*den(2)
      -GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL,2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL,2,n)
      -sum_(jjj,1,1+a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(1),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r=1, q_1=1 and p_1=1 (sommetjes equation 7.156)
id GG(R(?w,y?),X(?z,m?),RU(1,b?,?c),RL(1),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(1),1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL,2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,b,?c),RL,1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU,RL(b,?c),2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(1,b,?c),1,n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(b,?c),RL,1,n)
      -GG(R(?w,y,2),X(?z,m/2,2),RU,RL(b,?c),1,n)
      +GG(R(?w,y),X(?z,m),RU(1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=1, p_1<-1 and p_2>=0 (sommetjes equation 7.157)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(1),1,n?) = -abs_(a)*den(2)*g(nargs_(?c))*S(R(?w,y,-(2+b+abs_(a)),?c),X(?z,m/2,2),n)
      +abs_(a)*den(2)*g(nargs_(?c))*S(R(?w,y,-(2+abs_(a)),b,?c),X(?z,m/2,2,1),n)
      -abs_(a)*den(2)*TT(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL,2,n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,-2-b-abs_(a),?c),X(?z,m/2,2),n)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-2-abs_(a),b,?c),X(?z,m/2,2,1),n)
      -den(2)*TT(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(1),RL(?c),1+b,n)
      -sum_(jjj,2,1+abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*jjj)*den(2);
* k=1, s>1, r=1, q_1=1, p_1<-1 and p_2<0 (sommetjes equation 7.158)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(1),1,n?) = -abs_(a)*GG(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      -abs_(a)*den(2)*g(nargs_(?c))*S(R(?w,y,-(-2-abs_(a)-abs_(b)),?c),X(?z,m/2,2),n)
      +abs_(a)*den(2)*g(nargs_(?c))*S(R(?w,y,-(2+abs_(a)),b,?c),X(?z,m/2,2,1),n)
      -GG(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(1),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL,2,n)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-2-abs_(a),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2+abs_(a)+abs_(b),?c),X(?z,m/2,2),n)
      -sum_(jjj,2,1+abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*jjj)*den(2);
* k=1, s>1, r=1, q_1=1, p_1=-1 and p_2>=0 (sommetjes equation 7.159)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(1),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL,2,n)
      -g(nargs_(?c))*S(R(?w,y,-3-b,?c),X(?z,m/2,2),n)
      +g(nargs_(?c))*S(R(?w,y,-3,b,?c),X(?z,m/2,2,1),n)
      -TT(R(?w,y,2),X(?z,m/2,2),RU,RL(?c),1+b,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(1),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU,RL(b,?c),2,n);
* k=1, s>1, r=1, q_1=1, p_1=-1 and p_2<0 (sommetjes equation 7.160)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(1),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL,1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU,RL(-1,b,?c),1,n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL,2,n)
      -g(nargs_(?c))*S(R(?w,y,3+abs_(b),?c),X(?z,m/2,2),n)
      +g(nargs_(?c))*S(R(?w,y,-3,b,?c),X(?z,m/2,2,1),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU,RL(b,?c),2,n);
* k=1, s>1, r=1, q_1<-1, p_1>1 and p_2>=0 (sommetjes equation 7.161)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{>=0},?c),RL(d?{<-1}),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*g(nargs_(?c))*S(R(?w,y,1+b+a+abs_(d),?c),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(d),-1+a)*den(2)*g(nargs_(?c))*S(R(?w,y,1+a+abs_(d),b,?c),X(?z,m/2,2,1),n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*TT(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*g(nargs_(?c))*S(R(?w,y,1+b+a+abs_(d),?c),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(d),a)*den(2)*g(nargs_(?c))*S(R(?w,y,1+a+abs_(d),b,?c),X(?z,m/2,2,1),n)
      -binom_(-1+a+abs_(d),a)*den(2)*TT(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d),1,n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,1+a+abs_(d),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),a,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1+a,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r=1, q_1<-1, p_1>1 and p_2<0 (sommetjes equation 7.162)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{<0},?c),RL(d?{<-1}),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*g(nargs_(?c))*S(R(?w,y,-1-a-abs_(b)-abs_(d),?c),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(d),-1+a)*den(2)*g(nargs_(?c))*S(R(?w,y,1+a+abs_(d),b,?c),X(?z,m/2,2,1),n)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+a+abs_(d),a)*GG(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+a+abs_(d),a)*den(2)*g(nargs_(?c))*S(R(?w,y,-1-a-abs_(b)-abs_(d),?c),X(?z,m/2,2),n)
      +binom_(-1+a+abs_(d),a)*den(2)*g(nargs_(?c))*S(R(?w,y,1+a+abs_(d),b,?c),X(?z,m/2,2,1),n)
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d),1,n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,1+a+abs_(d),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),a,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1+a,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r=1, q_1<-1, p_1=1 and p_2>=0 (sommetjes equation 7.163)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{>=0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*den(2)*g(nargs_(?c))*S(R(?w,y,2+b+abs_(d),?c),X(?z,m/2,2),n)
      +(abs_(d)+2)*den(2)*g(nargs_(?c))*S(R(?w,y,2+abs_(d),b,?c),X(?z,m/2,2,1),n)
      -abs_(d)*den(2)*TT(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d),1,n)*den(2)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),1,b,?c),X(?z,m/2,2,1,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2+b+abs_(d),?c),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL,1+abs_(d),n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*jjj)*den(2);
* k=1, s>1, r=1, q_1<-1, p_1=1 and p_2<0 (sommetjes equation 7.164)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{<0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      -abs_(d)*den(2)*g(nargs_(?c))*S(R(?w,y,-2-abs_(b)-abs_(d),?c),X(?z,m/2,2),n)
      +(abs_(d)+2)*den(2)*g(nargs_(?c))*S(R(?w,y,2+abs_(d),b,?c),X(?z,m/2,2,1),n)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d),1,n)*den(2)
      -den(2)*g(nargs_(?c))*S(R(?w,y,-2-abs_(b)-abs_(d),?c),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),1,b,?c),X(?z,m/2,2,1,1),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL,1+abs_(d),n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL,1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*jjj)*den(2);
* k=1, s>1, r=1, q_1<-1, p_1<-1 and p_2>=0 (sommetjes equation 7.165)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(d?{<-1}),1,n?) = GG(R(?w,y,-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1+abs_(a),n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-1-abs_(a)-abs_(d),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),a,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1+abs_(d),n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL,jjj,n))*den(2);
* k=1, s>1, r=1, q_1<-1, p_1<-1 and p_2<0 (sommetjes equation 7.166)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(d?{<-1}),1,n?) = GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1+abs_(a),n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-1-abs_(a)-abs_(d),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),a,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1+abs_(d),n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL,jjj,n))*den(2);
* k=1, s>1, r=1, q_1<-1, p_1=-1 and p_2>=0 (sommetjes equation 7.167)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1,n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-2-abs_(d),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),-1,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(d),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL,jjj,n))*den(2);
* k=1, s>1, r=1, q_1<-1, p_1=-1 and p_2<0 (sommetjes equation 7.168)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(d?{<-1}),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU,RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d),RL(?c),1+abs_(b),n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-2-abs_(d),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,1+abs_(d),-1,b,?c),X(?z,m/2,2,1,1),n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL,1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n))*den(2)
      +sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL,jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL,jjj,n))*den(2);
* k=1, s>1, r=1, q_1=-1, p_1>1 and p_2>=0 (sommetjes equation 7.169)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{>=0},?c),RL(-1),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(-1),1,n)*den(2)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2+b+a,?c),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2+b+a,?c),X(?z,m/2,2),n)*a
      +2*den(2)*g(nargs_(?c))*S(R(?w,y,2+a,b,?c),X(?z,m/2,2,1),n)
      +den(2)*g(nargs_(?c))*S(R(?w,y,2+a,b,?c),X(?z,m/2,2,1),n)*a
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,a,b,?c),X(?z,m/2,2,1,1),n)
      -den(2)*TT(R(?w,y,-1-a),X(?z,m/2,2),RU,RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,-1-a),X(?z,m/2,2),RU,RL(?c),1+b,n)*a
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL,2,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1),RL(b,?c),jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r=1, q_1=-1, p_1>1 and p_2<0 (sommetjes equation 7.170)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{<0},?c),RL(-1),1,n?) = -GG(R(?w,y,-1-a),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,-1-a),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)*den(2)*a
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(-1),1,n)*den(2)
      -den(2)*g(nargs_(?c))*S(R(?w,y,-2-a-abs_(b),?c),X(?z,m/2,2),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,-2-a-abs_(b),?c),X(?z,m/2,2),n)*a
      +2*den(2)*g(nargs_(?c))*S(R(?w,y,2+a,b,?c),X(?z,m/2,2,1),n)
      +den(2)*g(nargs_(?c))*S(R(?w,y,2+a,b,?c),X(?z,m/2,2,1),n)*a
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,a,b,?c),X(?z,m/2,2,1,1),n)
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL,2,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1),RL(b,?c),jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r=1, q_1=-1, p_1=1 and p_2>=0 (sommetjes equation 7.171)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{>=0},?c),RL(-1),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(-1),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(b,?c),1,n)*den(2)
      -TT(R(?w,y,-2),X(?z,m/2,2),RU,RL(?c),1+b,n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,1,b,?c),X(?z,m/2,2,1,1),n)
      +3*den(2)*g(nargs_(?c))*S(R(?w,y,3,b,?c),X(?z,m/2,2,1),n)
      -g(nargs_(?c))*S(R(?w,y,b+3,?c),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL,2,n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=-1, p_1=1 and p_2<0 (sommetjes equation 7.172)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{<0},?c),RL(-1),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU,RL(?c),1+abs_(b),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(-1),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(b,?c),1,n)*den(2)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,1,b,?c),X(?z,m/2,2,1,1),n)
      +3*den(2)*g(nargs_(?c))*S(R(?w,y,3,b,?c),X(?z,m/2,2,1),n)
      -g(nargs_(?c))*S(R(?w,y,-(abs_(b)+3),?c),X(?z,m/2,2),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL,2,n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=-1, p_1<-1 and p_2>=0 (sommetjes equation 7.173)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(-1),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1,n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-(2+abs_(a)),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,a,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(-1),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r=1, q_1=-1, p_1<-1 and p_2<0 (sommetjes equation 7.174)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(-1),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL,1,n)*den(2)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(-1),RL(?c),1+abs_(b),n)*den(2)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-(2+abs_(a)),b,?c),X(?z,m/2,2,1),n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,a,b,?c),X(?z,m/2,2,1,1),n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL,2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU,RL(b,?c),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r=1, q_1=-1, p_1=-1 and p_2>=0 (sommetjes equation 7.175)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(-1),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU,RL(b,?c),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL,1,n)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,-1,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-3,b,?c),X(?z,m/2,2,1),n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL,2,n);
* k=1, s>1, r=1, q_1=-1, p_1=-1 and p_2<0 (sommetjes equation 7.176)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(-1),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU,RL(b,?c),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL,1,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1),RL(?c),1+abs_(b),n)*den(2)
      -den(2)*g(nargs_(?c))*S(R(?w,y,2,-1,b,?c),X(?z,m/2,2,1,1),n)
      +den(2)*g(nargs_(?c))*S(R(?w,y,-3,b,?c),X(?z,m/2,2,1),n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL,2,n);
**********
* k=1, s>1, r>1, q_1>1 and p_1>1 (sommetjes equation 7.177)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?,?c),RL(d?{>1},e?,?w),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+d,n)
      -sum_(jjj,1,1+d,binom_(-jjj+d+a,-1+a)*GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,1,1+a,binom_(-jjj+d+a,-1+d)*GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,a,binom_(-jjj+d+a,d)*GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,d,binom_(-jjj+d+a,a)*GG(R(?w,y,1-jjj+d+a),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1>1 and p_1=1 (sommetjes equation 7.178)
id GG(R(?w,y?),X(?z,m?),RU(1,b?,?c),RL(d?{>1},e?,?w),1,n?) = -GG(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)*d
      -GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)*den(2)
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),1+d,n)
      -sum_(jjj,1,1+d,GG(R(?w,y,2-jjj+d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,1,d,GG(R(?w,y,2-jjj+d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,1,d,GG(R(?w,y,2-jjj+d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      -sum_(jjj,1,d,GG(R(?w,y,2-jjj+d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*d;
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.179)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*den(2)*TT(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*TT(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*den(2)*TT(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*den(2)*TT(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.180)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*GG(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+d+abs_(a),abs_(a))*den(2)*TT(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+d+abs_(a),d)*GG(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+d+abs_(a),d)*den(2)*TT(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+d,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.181)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*den(2)*TT(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -binom_(-1+d+abs_(a),d)*GG(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -binom_(-1+d+abs_(a),d)*den(2)*TT(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+d,n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1>1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.182)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -binom_(-1+d+abs_(a),-1+d)*GG(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+d+abs_(a),abs_(a))*GG(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -binom_(-1+d+abs_(a),d)*GG(R(?w,y,-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -binom_(-1+d+abs_(a),d)*GG(R(?w,y,d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+d,n)
      +den(2)*TT(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+d,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+d,binom_(-jjj+d+abs_(a),-1+abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(a),binom_(-jjj+d+abs_(a),-1+d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),binom_(-jjj+d+abs_(a),d)*TT(R(?w,y,1-jjj+d+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,d,binom_(-jjj+d+abs_(a),abs_(a))*TT(R(?w,y,-1+jjj-d-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.183)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*TT(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)*d
      -den(2)*TT(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)*d
      -den(2)*TT(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)
      -2*sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*d;
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.184)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(d?{>1},e?{>=0},?w),1,n?) = -GG(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*d
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*TT(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)*d
      -den(2)*TT(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)
      -2*sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*d;
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.185)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -GG(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*d
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*TT(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)*d
      -den(2)*TT(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)
      -2*sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*d;
* k=1, s>1, r>1, q_1>1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.186)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(d?{>1},e?{<0},?w),1,n?) = -GG(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,-1-d),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*d
      -GG(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,1+d),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*d
      +GG(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+d,n)
      -den(2)*TT(R(?w,y,d),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)
      +sum_(jjj,1,d,GG(R(?w,y,1-jjj+d),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2)
      -2*sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,d,TT(R(?w,y,-2+jjj-d),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)*d;
* k=1, s>1, r>1, q_1=1 and p_1>1 (sommetjes equation 7.187)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?,?c),RL(1,e?,?w),1,n?) = -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)*a
      -GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)*den(2)
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(1,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+a,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)
      -2*sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,1,a,GG(R(?w,y,2-jjj+a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r>1, q_1=1 and p_1=1 (sommetjes equation 7.188)
id GG(R(?w,y?),X(?z,m?),RU(1,b?,?c),RL(1,e?,?w),1,n?) = -GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(1,e,?w),1,n)*den(2)
      -GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,e,?w),RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)
      +GG(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.189)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(1,e?{>=0},?w),1,n?) = -abs_(a)*den(2)*TT(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -abs_(a)*den(2)*TT(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*TT(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.190)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(1,e?{>=0},?w),1,n?) = -abs_(a)*GG(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -abs_(a)*den(2)*TT(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -GG(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*TT(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.191)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -abs_(a)*den(2)*TT(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*TT(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1=1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.192)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -abs_(a)*GG(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,1+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(a,b,?c),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(1,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,2-jjj+abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.193)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(1,e?{>=0},?w),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n)
      -TT(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -TT(R(?w,y,2),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+b,n);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.194)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(1,e?{>=0},?w),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n)
      -TT(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.195)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(1,e?{<0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n)
      -TT(R(?w,y,2),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+b,n);
* k=1, s>1, r>1, q_1=1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.196)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(1,e?{<0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(-1,b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)
      +GG(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(e,?w),RL(b,?c),2,n);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2>=0 and p_2>=0 (sommetjes equation 7.197)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*TT(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*TT(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*TT(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*den(2)*TT(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +den(2)*TT(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2>=0 and p_2<0 (sommetjes equation 7.198)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*den(2)*TT(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+a+abs_(d),a)*GG(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+a+abs_(d),a)*den(2)*TT(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +den(2)*TT(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+a,n)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2<0 and p_2>=0 (sommetjes equation 7.199)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*GG(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -binom_(-1+a+abs_(d),abs_(d))*den(2)*TT(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -binom_(-1+a+abs_(d),a)*GG(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -binom_(-1+a+abs_(d),a)*den(2)*TT(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      +GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +den(2)*TT(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+a,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1>1, q_2<0 and p_2<0 (sommetjes equation 7.200)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -binom_(-1+a+abs_(d),-1+a)*GG(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -binom_(-1+a+abs_(d),abs_(d))*GG(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+a+abs_(d),a)*GG(R(?w,y,-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -binom_(-1+a+abs_(d),a)*GG(R(?w,y,a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +den(2)*TT(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+a,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+a,binom_(-jjj+a+abs_(d),-1+abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,2,1+abs_(d),binom_(-jjj+a+abs_(d),-1+a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),binom_(-jjj+a+abs_(d),a)*TT(R(?w,y,1-jjj+a+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,a,binom_(-jjj+a+abs_(d),abs_(d))*TT(R(?w,y,-1+jjj-a-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2>=0 and p_2>=0 (sommetjes equation 7.201)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*den(2)*TT(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -abs_(d)*den(2)*TT(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*TT(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2>=0 and p_2<0 (sommetjes equation 7.202)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -abs_(d)*den(2)*TT(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*TT(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2<0 and p_2>=0 (sommetjes equation 7.203)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -abs_(d)*den(2)*TT(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -GG(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*TT(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=1, q_2<0 and p_2<0 (sommetjes equation 7.204)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -abs_(d)*GG(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,1+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(d,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),1,n)*den(2)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),1+abs_(d),n)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(1,b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,2-jjj+abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.205)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = den(2)*GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*GG(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.206)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +den(2)*GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*GG(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.207)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +den(2)*GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +den(2)*GG(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.208)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +den(2)*GG(R(?w,y,-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1+abs_(d),n)
      +den(2)*GG(R(?w,y,-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1+abs_(a),n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,1+abs_(a),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,1+abs_(d),binom_(-jjj+abs_(a)+abs_(d),-1+abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      -sum_(jjj,1,abs_(a),binom_(-jjj+abs_(a)+abs_(d),abs_(d))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      -sum_(jjj,1,abs_(d),binom_(-jjj+abs_(a)+abs_(d),abs_(a))*GG(R(?w,y,-1+jjj-abs_(a)-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(d,e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(a,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.209)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.210)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(d?{<-1},e?{>=0},?w),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +den(2)*TT(R(?w,y,abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.211)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1<-1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.212)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(d?{<-1},e?{<0},?w),1,n?) = -abs_(d)*GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(d)),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(d,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),1+abs_(d),n)
      -sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*abs_(d)*den(2)
      -2*sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n))*den(2)
      +sum_(jjj,1,abs_(d),GG(R(?w,y,-2+jjj-abs_(d)),X(?z,m/2,2),RU(b,?c),RL(e,?w),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(d),TT(R(?w,y,1-jjj+abs_(d)),X(?z,m/2,2),RU(-1,b,?c),RL(e,?w),jjj,n))*den(2);
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2>=0 and p_2>=0 (sommetjes equation 7.213)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      -den(2)*TT(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)*a
      -den(2)*TT(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)*a
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2>=0 and p_2<0 (sommetjes equation 7.214)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*a
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      -den(2)*TT(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)*a
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2<0 and p_2>=0 (sommetjes equation 7.215)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*a
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      -den(2)*TT(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)*a
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r>1, q_1=-1, p_1>1, q_2<0 and p_2<0 (sommetjes equation 7.216)
id GG(R(?w,y?),X(?z,m?),RU(a?{>1},b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)
      -GG(R(?w,y,-1-a),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)*den(2)*a
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,1+a),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)*den(2)*a
      +GG(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      -den(2)*TT(R(?w,y,a),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      +sum_(jjj,1,a,GG(R(?w,y,1-jjj+a),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2)
      -2*sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      -sum_(jjj,2,a,TT(R(?w,y,-2+jjj-a),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)*a;
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2>=0 and p_2>=0 (sommetjes equation 7.217)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      -TT(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -TT(R(?w,y,2),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2>=0 and p_2<0 (sommetjes equation 7.218)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      -TT(R(?w,y,2),X(?z,m/2,2),RU(b,?c),RL(?w),1+e,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2<0 and p_2>=0 (sommetjes equation 7.219)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)
      -TT(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(?c),1+b,n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=1, q_2<0 and p_2<0 (sommetjes equation 7.220)
id GG(R(?w,y?),X(?z,m?),RU(1,b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(?c),1+abs_(b),n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(-1,e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      -GG(R(?w,y,2),X(?z,m/2,2),RU(b,?c),RL(?w),1+abs_(e),n)
      -den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(b,?c),RL(e,?w),2,n)
      +TT(R(?w,y),X(?z,m),RU(1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2>=0 and p_2>=0 (sommetjes equation 7.221)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+b,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2>=0 and p_2<0 (sommetjes equation 7.222)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2<0 and p_2>=0 (sommetjes equation 7.223)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +den(2)*TT(R(?w,y,abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1=-1, p_1<-1, q_2<0 and p_2<0 (sommetjes equation 7.224)
id GG(R(?w,y?),X(?z,m?),RU(a?{<-1},b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -abs_(a)*GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      -GG(R(?w,y,-1-abs_(a)),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)*den(2)
      +GG(R(?w,y,abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(a,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +TT(R(?w,y),X(?z,m),RU(a,b,?c),RL(e,?w),2,n)
      -sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*abs_(a)*den(2)
      -2*sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n))*den(2)
      +sum_(jjj,1,abs_(a),GG(R(?w,y,-2+jjj-abs_(a)),X(?z,m/2,2),RU(e,?w),RL(b,?c),jjj,n)*jjj)*den(2)
      +sum_(jjj,2,abs_(a),TT(R(?w,y,1-jjj+abs_(a)),X(?z,m/2,2),RU(-1,e,?w),RL(b,?c),jjj,n))*den(2);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2>=0 and p_2>=0 (sommetjes equation 7.225)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+e,n)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2>=0 and p_2<0 (sommetjes equation 7.226)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(-1,e?{>=0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+e,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2<0 and p_2>=0 (sommetjes equation 7.227)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{>=0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +den(2)*TT(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+b,n)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n);
* k=1, s>1, r>1, q_1=-1, p_1=-1, q_2<0 and p_2<0 (sommetjes equation 7.228)
id GG(R(?w,y?),X(?z,m?),RU(-1,b?{<0},?c),RL(-1,e?{<0},?w),1,n?) = -GG(R(?w,y,-2),X(?z,m/2,2),RU(b,?c),RL(e,?w),1,n)
      -GG(R(?w,y,-2),X(?z,m/2,2),RU(e,?w),RL(b,?c),1,n)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,b,?c),RL(?w),1+abs_(e),n)*den(2)
      +GG(R(?w,y,1),X(?z,m/2,2),RU(-1,e,?w),RL(?c),1+abs_(b),n)*den(2)
      +TT(R(?w,y),X(?z,m),RU(-1,b,?c),RL(e,?w),2,n);
*--#]

*--#]

if ((match(once,GG(R(?a),X(?b),RU(c?,?d),RL(e?,?x),k?{>0},n?)))||(match(once,TT(R(?e),X(?x),RU(b?,?a),RL(d?,?c),k?{>1},n?))));
    redefine i "0";
endif;
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
.sort
#enddo

*--#[ Special cases
id GG(R,X,RU(?a),RL(?b),k?,1) = 0;
id GG(R,X,RU(?a),RL(?b),k?,0) = 0;
id TT(R,X,RU(?a),RL(?b),k?,1) = 0;
id TT(R,X,RU(?a),RL(?b),k?,0) = 0;
*--#]

*--#]

*--#[ 1 S-sum
#write " The recursion for two S-sums is finished and the recursion for one S-sum now starts"
*
* These first 44 id statements are there to initiate the recursion if we encounter an inverse binomial sum containing one S-sum. 
*

*--#[k=0

*--#[Sign altering
* Upper indices, k=0, p_1>=0 (sommetjes equation 7.10)
id TT(R,X,RU(m?{>=0},?a),RL,0,n?) = sign(n)*(n+1)*den(n+2)*TT(R,X,RU,RL(?a),m,n+1) 
        - S(R(m,?a),X(1),n)*g(nargs_(?a))*den(n+2);
* Upper indices, k=0, p_1<0 (sommetjes equation 7.11) 
id TT(R,X,RU(m?{<0},?a),RL,0,n?) = sign(n)*(n+1)*den(n+2)*GG(R,X,RU,RL(?a),abs_(m),n+1) 
        - S(R(m,?a),X(1),n)*g(nargs_(?a))*den(n+2);
* Lower indices, k=0, p_1>=0 (sommetjes equation 7.16)
id TT(R,X,RU,RL(m?{>=0},?a),0,n?) = sign(n)*(sign(n)*(n+1)*den(n+2)*TT(R,X,RU,RL(?a),m,n+1) - S(R(m,?a),X(1),n)*g(nargs_(?a))*den(n+2));
* Lower indices, k=0, p_1<0 (sommetjes equation 7.17) 
id TT(R,X,RU,RL(m?{<0},?a),0,n?) = sign(n)*(sign(n)*(n+1)*den(n+2)*GG(R,X,RU,RL(?a),abs_(m),n+1) - S(R(m,?a),X(1),n)*g(nargs_(?a))*den(n+2));
*--#]

*--#[Fixed sign
* Since for the case k=0 we have that the inverse binomial sums with 1 S-sum and upper indices are the same as the ones with lower indices,
* we minimize the amount of id statements by putting sending the inverse binomial sums with upper indices to the same inverse binomial sums
* with lower indices.
id GG(R,X,RU(a?,?b),RL,0,n?) = GG(R,X,RU,RL(a,?b),0,n);
* Lower indices, k=0, s=1 and p_1>1 (sommetjes equation 7.76)
id GG(R,X,RU,RL(a?{>1}),0,n?) = (n+1)*den(2)^(n+2)*GG(R(1),X(2),RU,RL,a,n)
        + sum_(jjj,1,a,den(2)*den(n)^(jjj)*(n+1)*sign(a-jjj))
        + sum_(jjj,1,a-1,(n+1)*den(2)^(n+2)*GG(R(a+1-jjj),X(2),RU,RL,jjj,n))
        + (n+1)*den(2)^(n+2)*GG(R(a),X(2),RU,RL,1,n)
        + den(2)*GG(R,X,RU,RL,a,n)
        + (n+1)*den(2)^(n+2)*(S(R(1,a),X(2,1),n) - S(R(a+1),X(2),n))
        - den(2)*S(R(a),X(1),n)
        + den(2)*sign(a);
* Lower indices, k=0, s=1 and p_1=1 (sommetjes equation 7.77)
id GG(R,X,RU,RL(1),0,n?) = den(2*n)
        + den(2)*GG(R,X,RU,RL,1,n)
        + (n+1)*den(2)^(n+1)*(S(R(1,1),X(1,2),n) + den(2)*S(R(1,1),X(2,1),n) - 3*den(2)*S(R(2),X(2),n))
        - den(2)*S(R(1),X(1),n);
* Lower indices, k=0, s=1 and p_1<-1 (sommetjes equation 7.78)
id GG(R,X,RU,RL(a?{<-1}),0,n?) = (n+1)*den(2)^(n+2)*TT(R(1),X(2),RU,RL,abs_(a),n)
        + sum_(jjj,2,abs_(a)-1,(n+1)*den(2)^(n+2)*TT(R(abs_(a)+1-jjj),X(2),RU,RL,jjj,n))
        + (n+1)*den(2)^(n+2)*(S(R(1,a),X(2,1),n) - S(R(abs_(a)+1),X(2),n) - 2*S(R(-(abs_(a)+1)),X(2),n))
        + sum_(jjj,1,abs_(a),den(2)*den(n)^(jjj)*(n+1)*sign(abs_(a)+n-jjj))
        + den(2)*TT(R,X,RU,RL,abs_(a),n)
        - den(2)*S(R(a),X(1),n)
        - den(2)*sign(abs_(a)+n+1);
* Lower indices, k=0, s=1 and p_1=-1 (sommetjes equation 7.79)
id GG(R,X,RU,RL(-1),0,n?) = den(2*n)*sign(n)
        + (n+1)*den(2)^(n+2)*(S(R(1,-1),X(2,1),n) - S(R(2),X(2),n) - 2*S(R(-2),X(2),n))
        + den(2)*TT(R,X,RU,RL,1,n)
        - den(2)*S(R(-1),X(1),n);
* Lower indices, k=0, s>1, p_1>1 and p_2>=0 (sommetjes equation 7.80)
id GG(R,X,RU,RL(a?{>1},b?{>=0},?c),0,n?) = sum_(jjj,1,a,(n+1)*den(2)^(n+2)*GG(R(a+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + (n+1)*den(2)^(n+2)*GG(R(a),X(2),RU(b,?c),RL,1,n)
        + sum_(jjj,1,a,den(2)*den(n)^(jjj)*(n+1)*sign(a-jjj)*S(R(b,?c),X(1),n)*g(nargs_(?c)))
        + (n+1)*den(2)^(n+2)*(S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c)) - S(R(a+1,b,?c),X(2,1),n)*g(nargs_(?c)))
        - den(2)*S(R(a,b,?c),X(1,1),n)*g(nargs_(?c))
        + den(2)*sign(a)*(S(R(b,?c),X(1),n+1)*g(nargs_(?c)) - den((n+1))^b*S(R(?c),X(),n+1)*g(nargs_(?c)))
        + den(2)*GG(R,X,RU,RL(b,?c),a,n);
* Lower indices, k=0, s>1, p_1>1 and p_2<0 (sommetjes equation 7.81)
id GG(R,X,RU,RL(a?{>1},b?{<0},?c),0,n?) =  sum_(jjj,1,a,(n+1)*den(2)^(n+2)*GG(R(a+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + (n+1)*den(2)^(n+2)*GG(R(a),X(2),RU(b,?c),RL,1,n)
        + sum_(jjj,1,a,den(2)*den(n)^(jjj)*(n+1)*sign(a-jjj)*S(R(b,?c),X(1),n)*g(nargs_(?c)))
        + (n+1)*den(2)^(n+2)*(S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c)) - S(R(a+1,b,?c),X(2,1),n)*g(nargs_(?c)))
        - den(2)*S(R(a,b,?c),X(1,1),n)*g(nargs_(?c))
        + den(2)*sign(a)*(S(R(b,?c),X(1),n+1)*g(nargs_(?c)) - sign(n+1)*den(n+1)^(abs_(b))*S(R(?c),X(),n+1)*g(nargs_(?c)))
        + den(2)*GG(R,X,RU,RL(b,?c),a,n);
* Lower indices, k=0, s>1, p_1=1 and p_2>=0 (sommetjes equation 7.82)
id GG(R,X,RU,RL(1,b?{>=0},?c),0,n?) = (n+1)*den(2)^(n+2)*GG(R(1),X(2),RU,RL(b,?c),1,n)
        + (n+1)*den(2)^(n+2)*GG(R(1),X(2),RU(b,?c),RL,1,n)
        + den(2)*GG(R,X,RU,RL(b,?c),1,n)
        + (n+1)*den(2)^(n+2)*(S(R(1,1,b,?c),X(2,1,1),n)*g(nargs_(?c)) - S(R(2,b,?c),X(2,1),n)*g(nargs_(?c)))
        - den(2)*S(R(1,b,?c),X(1,1),n)*g(nargs_(?c))
        - den(2)*(S(R(b,?c),X(1),n+1)*g(nargs_(?c)) - den(n+1)^(b)*S(R(?c),X(),n+1)*g(nargs_(?c)))
        + (n+1)*den(2*n)*S(R(b,?c),X(1),n)*g(nargs_(?c));
* Lower indices, k=0, s>1, p_1=1 and p_2<0 (sommetjes equation 7.83)
id GG(R,X,RU,RL(1,b?{<0},?c),0,n?) = (n+1)*den(2)^(n+2)*GG(R(1),X(2),RU,RL(b,?c),1,n)
        + (n+1)*den(2)^(n+2)*GG(R(1),X(2),RU(b,?c),RL,1,n)
        + den(2)*GG(R,X,RU,RL(b,?c),1,n)
        + (n+1)*den(2)^(n+2)*(S(R(1,1,b,?c),X(2,1,1),n)*g(nargs_(?c)) - S(R(2,b,?c),X(2,1),n)*g(nargs_(?c)))
        - den(2)*S(R(1,b,?c),X(1,1),n)*g(nargs_(?c))
        - den(2)*(S(R(b,?c),X(1),n+1)*g(nargs_(?c)) - sign(n+1)*den(n+1)^(abs_(b))*S(R(?c),X(),n+1)*g(nargs_(?c)))
        + (n+1)*den(2*n)*S(R(b,?c),X(1),n)*g(nargs_(?c));
* Lower indices, k=0, s>1, p_1<-1 and p_2>=0 (sommetjes equation 7.84)
id GG(R,X,RU,RL(a?{<-1},b?{>=0},?c),0,n?) = (n+1)*den(2)^(n+2)*TT(R(1),X(2),RU,RL(b,?c),abs_(a),n)
        + (n+1)*den(2)^(n+2)*TT(R(abs_(a)),X(2),RU,RL(?c),b+1,n)
        + sum_(jjj,2,abs_(a)-1,(n+1)*den(2)^(n+2)*TT(R(abs_(a)+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + den(2)*TT(R,X,RU,RL(b,?c),abs_(a),n)
        + (n+1)*den(2)^(n+2)*(S(R(-(abs_(a)+b+1),?c),X(2),n)*g(nargs_(?c)) + S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c)) - 2*S(R(-(abs_(a)+1),b,?c),X(2,1),n)*g(nargs_(?c)))
        + sum_(jjj,1,abs_(a),den(2)*den(n)^(jjj)*(n+1)*sign(abs_(a)-jjj+n)*S(R(b,?c),X(1),n)*g(nargs_(?c)))
        - den(2)*S(R(a,b,?c),X(1,1),n)*g(nargs_(?c))
        - den(2)*sign(abs_(a)+n+1)*(S(R(b,?c),X(1),n+1)*g(nargs_(?c)) - den(n+1)^b*S(R(?c),X(),n+1)*g(nargs_(?c)));
* Lower indices, k=0, s>1, p_1<-1 and p_2<0 (sommetjes equation 7.85)
id GG(R,X,RU,RL(a?{<-1},b?{<0},?c),0,n?) = (n+1)*den(2)^(n+2)*TT(R(1),X(2),RU,RL(b,?c),abs_(a),n)
        + sum_(jjj,2,abs_(a)-1,(n+1)*den(2)^(n+2)*TT(R(abs_(a)+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + (n+1)*den(2)^(n+2)*GG(R(abs_(a)),X(2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*TT(R,X,RU,RL(b,?c),abs_(a),n)
        + (n+1)*den(2)^(n+2)*(S(R(abs_(a)+abs_(b)+1,?c),X(2),n)*g(nargs_(?c)) + S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c)) - 2*S(R(-(abs_(a)+1),b,?c),X(2,1),n)*g(nargs_(?c)))
        - den(2)*S(R(a,b,?c),X(1,1),n)*g(nargs_(?c))
        + sum_(jjj,1,abs_(a),den(2)*den(n)^(jjj)*(n+1)*sign(abs_(a)-jjj+n)*S(R(b,?c),X(1),n)*g(nargs_(?c)))
        - den(2)*sign(abs_(a)+n+1)*S(R(b,?c),X(1),n+1)*g(nargs_(?c)) 
        + den(2)*den(n+1)^(abs_(b))*sign(abs_(a))*S(R(?c),X(),n+1)*g(nargs_(?c));
* Lower indices, k=0, s>1, p_1=-1 and p_2>=0 (sommetjes equation 7.86)
id GG(R,X,RU,RL(-1,b?{>=0},?c),0,n?) = (n+1)*den(2)^(n+2)*TT(R(1),X(2),RU,RL(?c),b+1,n)
        + den(2)*TT(R,X,RU,RL(b,?c),1,n)
        + (n+1)*den(2)^(n+2)*(S(R(-(b+2),?c),X(2),n)*g(nargs_(?c)) + S(R(1,-1,b,?c),X(2,1,1),n)*g(nargs_(?c)) - 2*S(R(-2,b,?c),X(2,1),n)*g(nargs_(?c)))
        + den(2*n)*(n+1)*sign(n)*S(R(b,?c),X(1),n)*g(nargs_(?c))
        - den(2)*S(R(-1,b,?c),X(1,1),n)*g(nargs_(?c))
        + den(2)*sign(n+1)*(S(R(b,?c),X(1),n+1)*g(nargs_(?c)) - den(n+1)^(b)*S(R(?c),X(),n+1)*g(nargs_(?c)));
* Lower indices, k=0, s>1, p_1=-1 and p_2<0 (sommetjes equation 7.87)
id GG(R,X,RU,RL(-1,b?{<0},?c),0,n?) = (n+1)*den(2)^(n+2)*GG(R(1),X(2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*TT(R,X,RU,RL(b,?c),1,n)
        - den(2)*S(R(-1,b,?c),X(1,1),n)*g(nargs_(?c))
        + (n+1)*den(2)^(n+2)*(S(R(abs_(b)+2,?c),X(2),n)*g(nargs_(?c)) + S(R(1,-1,b,?c),X(2,1,1),n)*g(nargs_(?c)) - 2*S(R(-2,b,?c),X(2,1),n)*g(nargs_(?c)))
        + den(2*n)*(n+1)*sign(n)*S(R(b,?c),X(1),n)*g(nargs_(?c))
        + den(2)*sign(n+1)*S(R(b,?c),X(1),n+1)*g(nargs_(?c)) 
        - den(2)*den(n+1)^(abs_(b))*S(R(?c),X(),n+1)*g(nargs_(?c));
*--#]

*--#]
.sort
*--#[k=1

*--#[Sign altering
* Upper indices, k=1, p_1>=0 (sommetjes equation 7.8)
repeat id TT(R,X,RU(m?{>=0},?a),RL,1,n?) = sign(n)*den(n+1)*TT(R,X,RU,RL(?a),m,n) 
        - den(n+1)*S(R(m,?a),X(1),n-1)*g(nargs_(?a));
* Upper indices, k=1, p_1<0 (sommetjes equation 7.9) 
repeat id TT(R,X,RU(m?{<0},?a),RL,1,n?) = sign(n)*den(n+1)*GG(R,X,RU,RL(?a),abs_(m),n) 
        - den(n+1)*S(R(m,?a),X(1),n-1)*g(nargs_(?a));
* Lower indices, k=1, p_1>=0 (sommetjes equation 7.14)
repeat id TT(R,X,RU,RL(m?{>=0},?a),1,n?) = -den(n+1)*TT(R,X,RU,RL(?a),m,n) 
        - sign(n)*den(n*(n+1))*S(R(m,?a),X(1),n-1)*g(nargs_(?a)) 
        + TT(R,X,RU,RL(?a),m+1,n);
* Lower indices, k=1, p_1<0 (sommetjes equation 7.15) 
repeat id TT(R,X,RU,RL(m?{<0},?a),1,n?) = -den(n+1)*GG(R,X,RU,RL(?a),abs_(m),n) 
        - sign(n)*den(n*(n+1))*S(R(m,?a),X(1),n-1)*g(nargs_(?a)) 
        + GG(R,X,RU,RL(?a),abs_(m)+1,n);
*--#]

*--#[Fixed sign
* Upper indices, k=1, s=1 and p_1>1 (sommetjes equation 7.65)
id GG(R,X,RU(a?{>1}),RL,1,n?) = den(2)^(n+1)*sum_(jjj,1,a,GG(R(a+1-jjj),X(2),RU,RL,jjj,n))
        + den(2)^(n+1)*GG(R(a),X(2),RU,RL,1,n)
        + den(2)^(n+1)*S(R(1,a),X(2,1),n)
        - den(2)^(n+1)*S(R(a+1),X(2),n);
* Upper indices, k=1, s=1 and p_1=1 (sommetjes equation 7.66)
id GG(R,X,RU(1),RL,1,n?) = den(2)^(n+1)*S(R(1,1),X(2,1),n)
        + den(2)^(n)*S(R(1,1),X(1,2),n)
        - 3*den(2)^(n+1)*S(R(2),X(2),n);
* Upper indices, k=1, s=1 and p_1<-1 (sommetjes equation 7.67)
id GG(R,X,RU(a?{<-1}),RL,1,n?) = den(2)^(n+1)*TT(R(1),X(2),RU,RL,abs_(a),n)
        + den(2)^(n+1)*sum_(jjj,2,abs_(a)-1,TT(R(abs_(a)+1-jjj),X(2),RU,RL,jjj,n))
        - den(2)^(n+1)*S(R(abs_(a)+1),X(2),n)
        + den(2)^(n+1)*S(R(1,a),X(2,1),n)
        - den(2)^(n)*S(R(-(abs_(a)+1)),X(2),n);
* Upper indices, k=1, s=1 and p_1=-1 (sommetjes equation 7.68)
id GG(R,X,RU(-1),RL,1,n?) = -den(2)^(n+1)*S(R(2),X(2),n)
        - den(2)^(n)*S(R(-2),X(2),n)
        + den(2)^(n+1)*S(R(1,-1),X(2,1),n);
* Upper indices, k=1, s>1 and p_1>1 (sommetjes equation 7.69)
id GG(R,X,RU(a?{>1},b?,?c),RL,1,n?) = den(2)^(n+1)*sum_(jjj,1,a,GG(R(a+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + den(2)^(n+1)*GG(R(a),X(2),RU(b,?c),RL,1,n)
        + den(2)^(n+1)*S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n+1)*S(R(a+1,b,?c),X(2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1 and p_1=1 (sommetjes equation 7.70)
id GG(R,X,RU(1,b?,?c),RL,1,n?) = den(2)^(n+1)*GG(R(1),X(2),RU,RL(b,?c),1,n)
        + den(2)^(n+1)*GG(R(1),X(2),RU(b,?c),RL,1,n)
        + den(2)^(n+1)*S(R(1,1,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n+1)*S(R(2,b,?c),X(2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1<-1 and p_2>=0 (sommetjes equation 7.71)
id GG(R,X,RU(a?{<-1},b?{>=0},?c),RL,1,n?) = den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),abs_(a),n)
        + den(2)^(n+1)*S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c))
        + den(2)^(n+1)*TT(R(abs_(a)),X(2),RU,RL(?c),b+1,n)
        + den(2)^(n+1)*sum_(jjj,2,abs_(a)-1,TT(R(abs_(a)+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + den(2)^(n+1)*S(R(-(abs_(a)+b+1),?c),X(2),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-(abs_(a)+1),b,?c),X(2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1<-1 and p_2<0 (sommetjes equation 7.72)
id GG(R,X,RU(a?{<-1},b?{<0},?c),RL,1,n?) = den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),abs_(a),n)
        + den(2)^(n+1)*sum_(jjj,2,abs_(a)-1,TT(R(abs_(a)+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + den(2)^(n+1)*GG(R(abs_(a)),X(2),RU,RL(?c),abs_(b)+1,n)
        + den(2)^(n+1)*S(R(abs_(a)+abs_(b)+1,?c),X(2),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-(abs_(a)+1),b,?c),X(2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1=-1 and p_2>=0 (sommetjes equation 7.73)
id GG(R,X,RU(-1,b?{>=0},?c),RL,1,n?) = den(2)^(n+1)*TT(R(1),X(2),RU,RL(?c),b+1,n)
        + den(2)^(n+1)*S(R(-(b+2),?c),X(2),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,-1,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-2,b,?c),X(2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1=-1 and p_2<0 (sommetjes equation 7.74)
id GG(R,X,RU(-1,b?{<0},?c),RL,1,n?) = den(2)^(n+1)*GG(R(1),X(2),RU,RL(?c),abs_(b)+1,n)
        + den(2)^(n+1)*S(R(abs_(b)+2,?c),X(2),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,-1,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-2,b,?c),X(2,1),n)*g(nargs_(?c));
* Lower indices, k=1, s=1 and p_1>1 (sommetjes equation 7.88)
id GG(R,X,RU,RL(a?{>1}),1,n?) = GG(R,X,RU,RL,a+1,n)
        + den(2)^(n+1)*sum_(jjj,1,a,GG(R(a+1-jjj),X(2),RU,RL,jjj,n))
        + den(2)^(n+1)*GG(R(a),X(2),RU,RL,1,n)
        + den(2)^(n+1)*S(R(1,a),X(2,1),n)
        - den(n)*S(R(a),X(1),n)
        - den(2)^(n+1)*S(R(a+1),X(2),n)
        + den(n)^(a+1);
* Lower indices, k=1, s=1 and p_1=1 (sommetjes equation 7.89)
id GG(R,X,RU,RL(1),1,n?) = GG(R,X,RU,RL,2,n)
        + den(2)^(n+1)*S(R(1,1),X(2,1),n)
        + den(2)^(n)*S(R(1,1),X(1,2),n)
        - den(n)*S(R(1),X(1),n)
        - 3*den(2)^(n+1)*S(R(2),X(2),n)
        + den(n)^2;
* Lower indices, k=1, s=1 and p_1<-1 (sommetjes equation 7.90)
id GG(R,X,RU,RL(a?{<-1}),1,n?) = TT(R,X,RU,RL,abs_(a)+1,n)
        + den(2)^(n+1)*TT(R(1),X(2),RU,RL,abs_(a),n)
        + den(2)^(n+1)*sum_(jjj,2,abs_(a)-1,TT(R(abs_(a)+1-jjj),X(2),RU,RL,jjj,n))
        - den(2)^(n+1)*S(R(abs_(a)+1),X(2),n)
        + den(2)^(n+1)*S(R(1,a),X(2,1),n)
        - den(n)*S(R(a),X(1),n)
        - den(2)^(n)*S(R(-(abs_(a)+1)),X(2),n)
        + sign(n)*den(n)^(abs_(a)+1);
* Lower indices, k=1, s=1 and p_1=-1 (sommetjes equation 7.91)
id GG(R,X,RU,RL(-1),1,n?) = TT(R,X,RU,RL,2,n)
        - den(2)^(n+1)*S(R(2),X(2),n)
        - den(2)^(n)*S(R(-2),X(2),n)
        + den(2)^(n+1)*S(R(1,-1),X(2,1),n)
        - den(n)*S(R(-1),X(1),n)
        + sign(n)*den(n)^2;
* Lower indices, k=1, s>1 and p_1>1 (sommetjes equation 7.92)
id GG(R,X,RU,RL(a?{>1},b?,?c),1,n?) = GG(R,X,RU,RL(b,?c),a+1,n)
        + den(2)^(n+1)*sum_(jjj,1,a,GG(R(a+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + den(2)^(n+1)*GG(R(a),X(2),RU(b,?c),RL,1,n)
        - den(n)*S(R(a,b,?c),X(1,1),n)*g(nargs_(?c))
        + den(n)^(a+1)*S(R(b,?c),X(1),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n+1)*S(R(a+1,b,?c),X(2,1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1 and p_1=1 (sommetjes equation 7.93)
id GG(R,X,RU,RL(1,b?,?c),1,n?) = GG(R,X,RU,RL(b,?c),2,n)
        + den(2)^(n+1)*GG(R(1),X(2),RU,RL(b,?c),1,n)
        + den(2)^(n+1)*GG(R(1),X(2),RU(b,?c),RL,1,n)
        + den(2)^(n+1)*S(R(1,1,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(n)*S(R(1,b,?c),X(1,1),n)*g(nargs_(?c))
        - den(2)^(n+1)*S(R(2,b,?c),X(2,1),n)*g(nargs_(?c))
        + den(n)^2*S(R(b,?c),X(1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1<-1 and p_2>=0 (sommetjes equation 7.94)
id GG(R,X,RU,RL(a?{<-1},b?{>=0},?c),1,n?) = TT(R,X,RU,RL(b,?c),abs_(a)+1,n)
        + den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),abs_(a),n)
        + den(2)^(n+1)*TT(R(abs_(a)),X(2),RU,RL(?c),b+1,n)
        + den(2)^(n+1)*sum_(jjj,2,abs_(a)-1,TT(R(abs_(a)+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + den(2)^(n+1)*S(R(-(abs_(a)+b+1),?c),X(2),n)*g(nargs_(?c))
        - den(n)*S(R(a,b,?c),X(1,1),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c))
        + sign(n)*den(n)^(abs_(a)+1)*S(R(b,?c),X(1),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-(abs_(a)+1),b,?c),X(2,1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1<-1 and p_2<0 (sommetjes equation 7.95)
id GG(R,X,RU,RL(a?{<-1},b?{<0},?c),1,n?) = TT(R,X,RU,RL(b,?c),abs_(a)+1,n)
        + den(2)^(n+1)*TT(R(1),X(2),RU,RL(b,?c),abs_(a),n)
        + den(2)^(n+1)*sum_(jjj,2,abs_(a)-1,TT(R(abs_(a)+1-jjj),X(2),RU,RL(b,?c),jjj,n))
        + den(2)^(n+1)*GG(R(abs_(a)),X(2),RU,RL(?c),abs_(b)+1,n)
        + den(2)^(n+1)*S(R(abs_(a)+abs_(b)+1,?c),X(2),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,a,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(n)*S(R(a,b,?c),X(1,1),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-(abs_(a)+1),b,?c),X(2,1),n)*g(nargs_(?c))
        + sign(n)*den(n)^(abs_(a)+1)*S(R(b,?c),X(1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1=-1 and p_2>=0 (sommetjes equation 7.96)
id GG(R,X,RU,RL(-1,b?{>=0},?c),1,n?) = TT(R,X,RU,RL(b,?c),2,n)
        + den(2)^(n+1)*TT(R(1),X(2),RU,RL(?c),b+1,n)
        + den(2)^(n+1)*S(R(-(b+2),?c),X(2),n)*g(nargs_(?c))
        - den(n)*S(R(-1,b,?c),X(1,1),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,-1,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-2,b,?c),X(2,1),n)*g(nargs_(?c))
        + sign(n)*den(n)^2*S(R(b,?c),X(1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1=-1 and p_2<0 (sommetjes equation 7.97)
id GG(R,X,RU,RL(-1,b?{<0},?c),1,n?) = TT(R,X,RU,RL(b,?c),2,n)
        + den(2)^(n+1)*GG(R(1),X(2),RU,RL(?c),abs_(b)+1,n)
        + den(2)^(n+1)*S(R(abs_(b)+2,?c),X(2),n)*g(nargs_(?c))
        - den(n)*S(R(-1,b,?c),X(1,1),n)*g(nargs_(?c))
        + den(2)^(n+1)*S(R(1,-1,b,?c),X(2,1,1),n)*g(nargs_(?c))
        - den(2)^(n)*S(R(-2,b,?c),X(2,1),n)*g(nargs_(?c))
        + sign(n)*den(n)^2*S(R(b,?c),X(1),n)*g(nargs_(?c));
*--#]

*--#]
.sort
*--#[k>1

*--#[Sign altering
* Lower indices, k>1 and p_1>=0 (sommetjes equation 7.12)
id TT(R,X,RU,RL(m?{>=0},?a),k?{>1},n?) = -sign(n)*den(n)^k*S(R(m,?a),X(1),n)*g(nargs_(?a))
        + 2*S(R(-k,m,?a),X(1,1),n)*g(nargs_(?a))
        - S(R(-(m+k),?a),X(1),n)*g(nargs_(?a))
        - TT(R(k-1),X(1),RU,RL(?a),m+1,n)
        - sum_(jjj,2,k-1,TT(R(k-jjj),X(1),RU,RL(m,?a),jjj,n));
* Lower indices, k>1 and p_1<0 (sommetjes equation 7.13) 
id TT(R,X,RU,RL(m?{<0},?a),k?{>1},n?) = -sign(n)*den(n)^k*S(R(m,?a),X(1),n)*g(nargs_(?a))
        + 2*S(R(-k,m,?a),X(1,1),n)*g(nargs_(?a))
        - S(R(abs_(m)+k,?a),X(1),n)*g(nargs_(?a))
        - GG(R(k-1),X(1),RU,RL(?a),abs_(m)+1,n)
        - sum_(jjj,2,k-1,TT(R(k-jjj),X(1),RU,RL(m,?a),jjj,n));
*--#]

*--#[Fixed sign
* Lower indices and k>1 (sommetjes equation 7.75)
id GG(R,X,RU,RL(a?,?b),k?{>1},n?) = S(R(k,a,?b),X(1,1),n)*g(nargs_(?b))
        - den(n)^k*S(R(a,?b),X(1),n)*g(nargs_(?b))
        - sum_(jjj,1,k-1,GG(R(k-jjj),X(1),RU,RL(a,?b),jjj,n))
        - GG(R(k-1),X(1),RU(a,?b),RL,1,n);
*--#]

*--#]

id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
.sort
*
* The one S-sum recursion 
*
#do i = 1,1

*--#[k>1

*--#[Sign altering
* Upper indices, k>1, p_1>=0 and s=1 (sommetjes equation 7.4)
id TT(R(?c),X(?x),RU(m?{>=0}),RL,k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?c,m+k-jjj),X(?x,1),RU,RL,jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?c,-(m+k-jjj)),X(?x,1),RU,RL,jjj,n))
        - sum_(jjj,2,k-1,TT(R(?c,k-jjj),X(?x,1),RU(m),RL,jjj,n))
        - TT(R(?c,-(k-1)),X(?x,1),RU,RL,m+1,n)
        - binom_(m+k-1,m)*(S(R(?c,m+k),X(?x,1),n) + S(R(?c,-(m+k)),X(?x,1),n))
        + S(R(?c,k,m),X(?x,1,1),n)
        - S(R(?c,m+k),X(?x,1),n);
* Upper indices, k>1, p_1>=0, p_2>=0 and s>1 (sommetjes equation 7.5)
id TT(R(?c),X(?x),RU(m?{>=0},d?{>=0},?a),RL,k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?c,m+k-jjj),X(?x,1),RU(d,?a),RL,jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?c,-(m+k-jjj)),X(?x,1),RU,RL(d,?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?c,k-jjj),X(?x,1),RU(m,d,?a),RL,jjj,n))
        + binom_(m+k-1,m)*TT(R(?c,-(m+k-1)),X(?x,1),RU,RL(?a),d+1,n)
        - TT(R(?c,-(k-1)),X(?x,1),RU,RL(d,?a),m+1,n)
        - binom_(m+k-1,m)*(S(R(?c,m+k,d,?a),X(?x,1,1),n)*g(nargs_(?a)) - S(R(?c,m+d+k,?a),X(?x,1),n)*g(nargs_(?a)))
        + S(R(?c,k,m,d,?a),X(?x,1,1,1),n)*g(nargs_(?a))
        - S(R(?c,m+k,d,?a),X(?x,1,1),n)*g(nargs_(?a));
* Upper indices, k>1, p_1>=0, p_2<0 and s>1 (sommetjes equation 7.6) 
id TT(R(?c),X(?x),RU(m?{>=0},d?{<0},?a),RL,k?{>1},n?) = sum_(jjj,2,k,binom_(m+k-jjj,m)*TT(R(?c,m+k-jjj),X(?x,1),RU(d,?a),RL,jjj,n))
        + sum_(jjj,2,m+1,binom_(m+k-jjj,k-1)*TT(R(?c,-(m+k-jjj)),X(?x,1),RU,RL(d,?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?c,k-jjj),X(?x,1),RU(m,d,?a),RL,jjj,n))
        + binom_(m+k-1,m)*GG(R(?c,-(m+k-1)),X(?x,1),RU,RL(?a),abs_(d)+1,n)
        - TT(R(?c,-(k-1)),X(?x,1),RU,RL(d,?a),m+1,n)
        - binom_(m+k-1,m)*(S(R(?c,m+k,d,?a),X(?x,1,1),n)*g(nargs_(?a)) - S(R(?c,-(m+abs_(d)+k),?a),X(?x,1),n)*g(nargs_(?a)))
        + S(R(?c,k,m,d,?a),X(?x,1,1,1),n)*g(nargs_(?a))
        - S(R(?c,m+k,d,?a),X(?x,1,1),n)*g(nargs_(?a));
* Upper indices, k>1 and p_1<0 (sommetjes equation 7.7) 
id TT(R(?c),X(?x),RU(m?{<0},?a),RL,k?{>1},n?) = sum_(jjj,1,k,binom_(abs_(m)+k-jjj,abs_(m))*GG(R(?c,-(abs_(m)+k-jjj)),X(?x,1),RU(?a),RL,jjj,n))
        + sum_(jjj,1,abs_(m)+1,binom_(abs_(m)+k-jjj,k-1)*GG(R(?c,-(abs_(m)+k-jjj)),X(?x,1),RU,RL(?a),jjj,n))
        - sum_(jjj,2,k-1,TT(R(?c,k-jjj),X(?x,1),RU(m,?a),RL,jjj,n))
        - GG(R(?c,-(k-1)),X(?x,1),RU,RL(?a),abs_(m)+1,n)
        + S(R(?c,k,m,?a),X(?x,1,1),n)*g(nargs_(?a))
        - S(R(?c,-(abs_(m)+k),?a),X(?x,1),n)*g(nargs_(?a));
* Lower indices, k>1 and p_1>=0 (sommetjes equation 7.12). Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id TT(R(?c,d?{>=0}),X(?x,y?),RU,RL(m?{>=0},?a),k?{>1},n?) = - S(R(?c,-(d+k),m,?a),X(?x,y,1),n)*g(nargs_(?a))
        + 2*S(R(?c,d,-k,m,?a),X(?x,y,1,1),n)*g(nargs_(?a))
        - S(R(?c,d,-(m+k),?a),X(?x,y,1),n)*g(nargs_(?a))
        - TT(R(?c,d,k-1),X(?x,y,1),RU,RL(?a),m+1,n)
        - sum_(jjj,2,k-1,TT(R(?c,d,k-jjj),X(?x,y,1),RU,RL(m,?a),jjj,n));
id TT(R(?c,d?{<0}),X(?x,y?),RU,RL(m?{>=0},?a),k?{>1},n?) = - S(R(?c,abs_(d)+k,m,?a),X(?x,y,1),n)*g(nargs_(?a))
        + 2*S(R(?c,d,-k,m,?a),X(?x,y,1,1),n)*g(nargs_(?a))
        - S(R(?c,d,-(m+k),?a),X(?x,y,1),n)*g(nargs_(?a))
        - TT(R(?c,d,k-1),X(?x,y,1),RU,RL(?a),m+1,n)
        - sum_(jjj,2,k-1,TT(R(?c,d,k-jjj),X(?x,y,1),RU,RL(m,?a),jjj,n));
* Lower indices, k>1 and p_1<0 (sommetjes equation 7.13). Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero. 
id TT(R(?c,d?{>=0}),X(?x,y?),RU,RL(m?{<0},?a),k?{>1},n?) = - S(R(?c,-(d+k),m,?a),X(?x,y,1),n)*g(nargs_(?a))
        + 2*S(R(?c,d,-k,m,?a),X(?x,y,1,1),n)*g(nargs_(?a))
        - S(R(?c,d,abs_(m)+k,?a),X(?x,y,1),n)*g(nargs_(?a))
        - GG(R(?c,d,k-1),X(?x,y,1),RU,RL(?a),abs_(m)+1,n)
        - sum_(jjj,2,k-1,TT(R(?c,d,k-jjj),X(?x,y,1),RU,RL(m,?a),jjj,n));
id TT(R(?c,d?{<0}),X(?x,y?),RU,RL(m?{<0},?a),k?{>1},n?) = - S(R(?c,abs_(d)+k,m,?a),X(?x,y,1),n)*g(nargs_(?a))
        + 2*S(R(?c,d,-k,m,?a),X(?x,y,1,1),n)*g(nargs_(?a))
        - S(R(?c,d,abs_(m)+k,?a),X(?x,y,1),n)*g(nargs_(?a))
        - GG(R(?c,d,k-1),X(?x,y,1),RU,RL(?a),abs_(m)+1,n)
        - sum_(jjj,2,k-1,TT(R(?c,d,k-jjj),X(?x,y,1),RU,RL(m,?a),jjj,n));
*--#]

*--#[Fixed sign
* Upper indices, k>1 and p_1>=0 (sommetjes equation 7.49)
id GG(R(?d),X(?e),RU(a?{>=0},?b),RL,k?{>1},n?) = sum_(jjj,1,k,binom_(k+a-jjj,a)*GG(R(?d,k+a-jjj),X(?e,1),RU(?b),RL,jjj,n))
        + sum_(jjj,1,a+1,binom_(k+a-jjj,k-1)*GG(R(?d,k+a-jjj),X(?e,1),RU,RL(?b),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?d,k-jjj),X(?e,1),RU(a,?b),RL,jjj,n))
        - GG(R(?d,k-1),X(?e,1),RU,RL(a,?b),1,n);
* Upper indices, k>1, p_1<0 and s=1 (sommetjes equation 7.50)
id GG(R(?d),X(?e),RU(a?{<0}),RL,k?{>1},n?) = sum_(jjj,2,k,binom_(k+abs_(a)-jjj,abs_(a))*TT(R(?d,-(k+abs_(a)-jjj)),X(?e,1),RU,RL,jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(k+abs_(a)-jjj,k-1)*TT(R(?d,k+abs_(a)-jjj),X(?e,1),RU,RL,jjj,n))
        - sum_(jjj,1,k-1,GG(R(?d,k-jjj),X(?e,1),RU(a),RL,jjj,n))
        - GG(R(?d,k-1),X(?e,1),RU,RL(a),1,n)
        - binom_(k+abs_(a)-1,k-1)*(S(R(?d,k+abs_(a)),X(?e,1),n) + S(R(?d,-(k+abs_(a))),X(?e,1),n));
* Upper indices, k>1, p_1<0, s>1 and p_2>=0 (sommetjes equation 7.51)
id GG(R(?d),X(?e),RU(a?{<0},b?{>=0},?c),RL,k?{>1},n?) = sum_(jjj,2,k,binom_(k+abs_(a)-jjj,abs_(a))*TT(R(?d,-(k+abs_(a)-jjj)),X(?e,1),RU(b,?c),RL,jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(k+abs_(a)-jjj,k-1)*TT(R(?d,k+abs_(a)-jjj),X(?e,1),RU,RL(b,?c),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?d,k-jjj),X(?e,1),RU(a,b,?c),RL,jjj,n))
        - GG(R(?d,k-1),X(?e,1),RU,RL(a,b,?c),1,n)
        + binom_(k+abs_(a)-1,abs_(a))*TT(R(?d,k+abs_(a)-1),X(?e,1),RU,RL(?c),b+1,n)
        - binom_(k+abs_(a)-1,abs_(a))*(S(R(?d,-(k+abs_(a)),b,?c),X(?e,1,1),n)*g(nargs_(?c)) - S(R(?d,-(k+abs_(a)+b),?c),X(?e,1),n)*g(nargs_(?c)));
* Upper indices, k>1, p_1<0, s>1 and p_2<0 (sommetjes equation 7.52)
id GG(R(?d),X(?e),RU(a?{<0},b?{<0},?c),RL,k?{>1},n?) = sum_(jjj,2,k,binom_(k+abs_(a)-jjj,abs_(a))*TT(R(?d,-(k+abs_(a)-jjj)),X(?e,1),RU(b,?c),RL,jjj,n))
        + sum_(jjj,2,abs_(a)+1,binom_(k+abs_(a)-jjj,k-1)*TT(R(?d,k+abs_(a)-jjj),X(?e,1),RU,RL(b,?c),jjj,n))
        - sum_(jjj,1,k-1,GG(R(?d,k-jjj),X(?e,1),RU(a,b,?c),RL,jjj,n))
        - GG(R(?d,k-1),X(?e,1),RU,RL(a,b,?c),1,n)
        + binom_(k+abs_(a)-1,abs_(a))*GG(R(?d,k+abs_(a)-1),X(?e,1),RU,RL(?c),abs_(b)+1,n)
        - binom_(k+abs_(a)-1,abs_(a))*(S(R(?d,-(k+abs_(a)),b,?c),X(?e,1,1),n)*g(nargs_(?c)) - S(R(?d,k+abs_(a)+abs_(b),?c),X(?e,1),n)*g(nargs_(?c)));
* Lower indices and k>1 (sommetjes equation 7.75) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(a?,?b),k?{>1},n?) = S(R(?d,y,k,a,?b),X(?e,z,1,1),n)*g(nargs_(?b))
        - S(R(?d,y+k,a,?b),X(?e,z,1),n)*g(nargs_(?b))
        - sum_(jjj,1,k-1,GG(R(?d,y,k-jjj),X(?e,z,1),RU,RL(a,?b),jjj,n))
        - GG(R(?d,y,k-1),X(?e,z,1),RU(a,?b),RL,1,n);
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(a?,?b),k?{>1},n?) = S(R(?d,y,k,a,?b),X(?e,z,1,1),n)*g(nargs_(?b))
        - S(R(?d,-(abs_(y)+k),a,?b),X(?e,z,1),n)*g(nargs_(?b))
        - sum_(jjj,1,k-1,GG(R(?d,y,k-jjj),X(?e,z,1),RU,RL(a,?b),jjj,n))
        - GG(R(?d,y,k-1),X(?e,z,1),RU(a,?b),RL,1,n);
*--#]

*--#]
.sort
*--#[k=1

*--#[Fixed sign
* Upper indices, k=1, s=1 and p_1>1 (sommetjes equation 7.65)
id GG(R(?d,y?),X(?e,z?),RU(a?{>1}),RL,1,n?) = den(2)*sum_(jjj,1,a,GG(R(?d,y,a+1-jjj),X(?e,z/2,2),RU,RL,jjj,n))
        + den(2)*GG(R(?d,y,a),X(?e,z/2,2),RU,RL,1,n)
        + den(2)*S(R(?d,y,1,a),X(?e,z/2,2,1),n)
        - den(2)*S(R(?d,y,a+1),X(?e,z/2,2),n);
* Upper indices, k=1, s=1 and p_1=1 (sommetjes equation 7.66)
id GG(R(?d,y?),X(?e,z?),RU(1),RL,1,n?) = den(2)*S(R(?d,y,1,1),X(?e,z/2,2,1),n)
        + S(R(?d,y,1,1),X(?e,z/2,1,2),n)
        - 3*den(2)*S(R(?d,y,2),X(?e,z/2,2),n);
* Upper indices, k=1, s=1 and p_1<-1 (sommetjes equation 7.67)
id GG(R(?d,y?),X(?e,z?),RU(a?{<-1}),RL,1,n?) = den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL,abs_(a),n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL,jjj,n))
        - den(2)*S(R(?d,y,abs_(a)+1),X(?e,z/2,2),n)
        + den(2)*S(R(?d,y,1,a),X(?e,z/2,2,1),n)
        - S(R(?d,y,-(abs_(a)+1)),X(?e,z/2,2),n);
* Upper indices, k=1, s=1 and p_1=-1 (sommetjes equation 7.68)
id GG(R(?d,y?),X(?e,z?),RU(-1),RL,1,n?) = -den(2)*S(R(?d,y,2),X(?e,z/2,2),n)
        - S(R(?d,y,-2),X(?e,z/2,2),n)
        + den(2)*S(R(?d,y,1,-1),X(?e,z/2,2,1),n);
* Upper indices, k=1, s>1 and p_1>1 (sommetjes equation 7.69)
id GG(R(?d,y?),X(?e,z?),RU(a?{>1},b?,?c),RL,1,n?) = den(2)*sum_(jjj,1,a,GG(R(?d,y,a+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*GG(R(?d,y,a),X(?e,z/2,2),RU(b,?c),RL,1,n)
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - den(2)*S(R(?d,y,a+1,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1 and p_1=1 (sommetjes equation 7.70)
id GG(R(?d,y?),X(?e,z?),RU(1,b?,?c),RL,1,n?) = den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),1,n)
        + den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU(b,?c),RL,1,n)
        + den(2)*S(R(?d,y,1,1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - den(2)*S(R(?d,y,2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1<-1 and p_2>=0 (sommetjes equation 7.71)
id GG(R(?d,y?),X(?e,z?),RU(a?{<-1},b?{>=0},?c),RL,1,n?) = den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),abs_(a),n)
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        + den(2)*TT(R(?d,y,abs_(a)),X(?e,z/2,2),RU,RL(?c),b+1,n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*S(R(?d,y,-(abs_(a)+b+1),?c),X(?e,z/2,2),n)*g(nargs_(?c))
        - S(R(?d,y,-(abs_(a)+1),b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1<-1 and p_2<0 (sommetjes equation 7.72)
id GG(R(?d,y?),X(?e,z?),RU(a?{<-1},b?{<0},?c),RL,1,n?) = den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),abs_(a),n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*GG(R(?d,y,abs_(a)),X(?e,z/2,2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*S(R(?d,y,abs_(a)+abs_(b)+1,?c),X(?e,z/2,2),n)*g(nargs_(?c)) 
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-(abs_(a)+1),b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1=-1 and p_2>=0 (sommetjes equation 7.73)
id GG(R(?d,y?),X(?e,z?),RU(-1,b?{>=0},?c),RL,1,n?) = den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(?c),b+1,n)
        + den(2)*S(R(?d,y,-(b+2),?c),X(?e,z/2,2),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,-1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Upper indices, k=1, s>1, p_1=-1 and p_2<0 (sommetjes equation 7.74)
id GG(R(?d,y?),X(?e,z?),RU(-1,b?{<0},?c),RL,1,n?) = den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*S(R(?d,y,abs_(b)+2,?c),X(?e,z/2,2),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,-1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Lower indices, k=1, s=1 and p_1>1 (sommetjes equation 7.88) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(a?{>1}),1,n?) = GG(R(?d,y),X(?e,z),RU,RL,a+1,n)
        + den(2)*sum_(jjj,1,a,GG(R(?d,y,a+1-jjj),X(?e,z/2,2),RU,RL,jjj,n))
        + den(2)*GG(R(?d,y,a),X(?e,z/2,2),RU,RL,1,n)
        + den(2)*S(R(?d,y,1,a),X(?e,z/2,2,1),n)
        - S(R(?d,y+1,a),X(?e,z,1),n)
        - den(2)*S(R(?d,y,a+1),X(?e,z/2,2),n)
        + S(R(?d,y+a+1),X(?e,z),n);
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(a?{>1}),1,n?) = GG(R(?d,y),X(?e,z),RU,RL,a+1,n)
        + den(2)*sum_(jjj,1,a,GG(R(?d,y,a+1-jjj),X(?e,z/2,2),RU,RL,jjj,n))
        + den(2)*GG(R(?d,y,a),X(?e,z/2,2),RU,RL,1,n)
        + den(2)*S(R(?d,y,1,a),X(?e,z/2,2,1),n)
        - S(R(?d,-(abs_(y)+1),a),X(?e,z,1),n)
        - den(2)*S(R(?d,y,a+1),X(?e,z/2,2),n)
        + S(R(?d,-(abs_(y)+a+1)),X(?e,z),n);
* Lower indices, k=1, s=1 and p_1=1 (sommetjes equation 7.89) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(1),1,n?) = GG(R(?d,y),X(?e,z),RU,RL,2,n)
        + den(2)*S(R(?d,y,1,1),X(?e,z/2,2,1),n)
        + S(R(?d,y,1,1),X(?e,z/2,1,2),n)
        - S(R(?d,y+1,1),X(?e,z,1),n)
        - 3*den(2)*S(R(?d,y,2),X(?e,z/2,2),n)
        + S(R(?d,y+2),X(?e,z),n);
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(1),1,n?) = GG(R(?d,y),X(?e,z),RU,RL,2,n)
        + den(2)*S(R(?d,y,1,1),X(?e,z/2,2,1),n)
        + S(R(?d,y,1,1),X(?e,z/2,1,2),n)
        - S(R(?d,-(abs_(y)+1),1),X(?e,z,1),n)
        - 3*den(2)*S(R(?d,y,2),X(?e,z/2,2),n)
        + S(R(?d,-(abs_(y)+2)),X(?e,z),n);
* Lower indices, k=1, s=1 and p_1<-1 (sommetjes equation 7.90) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(a?{<-1}),1,n?) = TT(R(?d,y),X(?e,z),RU,RL,abs_(a)+1,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL,abs_(a),n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL,jjj,n))
        - den(2)*S(R(?d,y,abs_(a)+1),X(?e,z/2,2),n)
        + den(2)*S(R(?d,y,1,a),X(?e,z/2,2,1),n)
        - S(R(?d,y+1,a),X(?e,z,1),n)
        - S(R(?d,y,-(abs_(a)+1)),X(?e,z/2,2),n)
        + S(R(?d,-(y+abs_(a)+1)),X(?e,z),n);
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(a?{<-1}),1,n?) = TT(R(?d,y),X(?e,z),RU,RL,abs_(a)+1,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL,abs_(a),n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL,jjj,n))
        - den(2)*S(R(?d,y,abs_(a)+1),X(?e,z/2,2),n)
        + den(2)*S(R(?d,y,1,a),X(?e,z/2,2,1),n)
        - S(R(?d,-(abs_(y)+1),a),X(?e,z,1),n)
        - S(R(?d,y,-(abs_(a)+1)),X(?e,z/2,2),n)
        + S(R(?d,abs_(y)+abs_(a)+1),X(?e,z),n);
* Lower indices, k=1, s=1 and p_1=-1 (sommetjes equation 7.91) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(-1),1,n?) = TT(R(?d,y),X(?e,z),RU,RL,2,n)
        - den(2)*S(R(?d,y,2),X(?e,z/2,2),n)
        - S(R(?d,y,-2),X(?e,z/2,2),n)
        + den(2)*S(R(?d,y,1,-1),X(?e,z/2,2,1),n)
        - S(R(?d,y+1,-1),X(?e,z,1),n)
        + S(R(?d,-(y+2)),X(?e,z),n);
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(-1),1,n?) = TT(R(?d,y),X(?e,z),RU,RL,2,n)
        - den(2)*S(R(?d,y,2),X(?e,z/2,2),n)
        - S(R(?d,y,-2),X(?e,z/2,2),n)
        + den(2)*S(R(?d,y,1,-1),X(?e,z/2,2,1),n)
        - S(R(?d,-(abs_(y)+1),-1),X(?e,z,1),n)
        + S(R(?d,abs_(y)+2),X(?e,z),n);
* Lower indices, k=1, s>1 and p_1>1 (sommetjes equation 7.92) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(a?{>1},b?,?c),1,n?) = GG(R(?d,y),X(?e,z),RU,RL(b,?c),a+1,n)
        + den(2)*sum_(jjj,1,a,GG(R(?d,y,a+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*GG(R(?d,y,a),X(?e,z/2,2),RU(b,?c),RL,1,n)
        - S(R(?d,y+1,a,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + S(R(?d,y+a+1,b,?c),X(?e,z,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - den(2)*S(R(?d,y,a+1,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(a?{>1},b?,?c),1,n?) = GG(R(?d,y),X(?e,z),RU,RL(b,?c),a+1,n)
        + den(2)*sum_(jjj,1,a,GG(R(?d,y,a+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*GG(R(?d,y,a),X(?e,z/2,2),RU(b,?c),RL,1,n)
        - S(R(?d,-(abs_(y)+1),a,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + S(R(?d,-(abs_(y)+a+1),b,?c),X(?e,z,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - den(2)*S(R(?d,y,a+1,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1 and p_1=1 (sommetjes equation 7.93) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(1,b?,?c),1,n?) = GG(R(?d,y),X(?e,z),RU,RL(b,?c),2,n)
        + den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),1,n)
        + den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU(b,?c),RL,1,n)
        + den(2)*S(R(?d,y,1,1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y+1,1,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        - den(2)*S(R(?d,y,2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,y+2,b,?c),X(?e,z,1),n)*g(nargs_(?c));
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(1,b?,?c),1,n?) = GG(R(?d,y),X(?e,z),RU,RL(b,?c),2,n)
        + den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),1,n)
        + den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU(b,?c),RL,1,n)
        + den(2)*S(R(?d,y,1,1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,-(abs_(y)+1),1,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        - den(2)*S(R(?d,y,2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,-(abs_(y)+2),b,?c),X(?e,z,1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1<-1 and p_2>=0 (sommetjes equation 7.94) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(a?{<-1},b?{>=0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),abs_(a)+1,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),abs_(a),n)
        + den(2)*TT(R(?d,y,abs_(a)),X(?e,z/2,2),RU,RL(?c),b+1,n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*S(R(?d,y,-(abs_(a)+b+1),?c),X(?e,z/2,2),n)*g(nargs_(?c))
        - S(R(?d,y+1,a,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        + S(R(?d,-(y+abs_(a)+1),b,?c),X(?e,z,1),n)*g(nargs_(?c))
        - S(R(?d,y,-(abs_(a)+1),b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(a?{<-1},b?{>=0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),abs_(a)+1,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),abs_(a),n)
        + den(2)*TT(R(?d,y,abs_(a)),X(?e,z/2,2),RU,RL(?c),b+1,n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*S(R(?d,y,-(abs_(a)+b+1),?c),X(?e,z/2,2),n)*g(nargs_(?c))
        - S(R(?d,-(abs_(y)+1),a,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        + S(R(?d,abs_(y)+abs_(a)+1,b,?c),X(?e,z,1),n)*g(nargs_(?c))
        - S(R(?d,y,-(abs_(a)+1),b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1<-1 and p_2<0 (sommetjes equation 7.95) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(a?{<-1},b?{<0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),abs_(a)+1,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),abs_(a),n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*GG(R(?d,y,abs_(a)),X(?e,z/2,2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*S(R(?d,y,abs_(a)+abs_(b)+1,?c),X(?e,z/2,2),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y+1,a,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-(abs_(a)+1),b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,-(y+abs_(a)+1),b,?c),X(?e,z,1),n)*g(nargs_(?c));
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(a?{<-1},b?{<0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),abs_(a)+1,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(b,?c),abs_(a),n)
        + den(2)*sum_(jjj,2,abs_(a)-1,TT(R(?d,y,abs_(a)+1-jjj),X(?e,z/2,2),RU,RL(b,?c),jjj,n))
        + den(2)*GG(R(?d,y,abs_(a)),X(?e,z/2,2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*S(R(?d,y,abs_(a)+abs_(b)+1,?c),X(?e,z/2,2),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,a,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,-(abs_(y)+1),a,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-(abs_(a)+1),b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,abs_(y)+abs_(a)+1,b,?c),X(?e,z,1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1=-1 and p_2>=0 (sommetjes equation 7.96) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(-1,b?{>=0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),2,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(?c),b+1,n)
        + den(2)*S(R(?d,y,-(b+2),?c),X(?e,z/2,2),n)*g(nargs_(?c))
        - S(R(?d,y+1,-1,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,-1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,-(y+2),b,?c),X(?e,z,1),n)*g(nargs_(?c));
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(-1,b?{>=0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),2,n)
        + den(2)*TT(R(?d,y,1),X(?e,z/2,2),RU,RL(?c),b+1,n)
        + den(2)*S(R(?d,y,-(b+2),?c),X(?e,z/2,2),n)*g(nargs_(?c))
        - S(R(?d,-(abs_(y)+1),-1,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,-1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,abs_(y)+2,b,?c),X(?e,z,1),n)*g(nargs_(?c));
* Lower indices, k=1, s>1, p_1=-1 and p_2<0 (sommetjes equation 7.97) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?d,y?{>=0}),X(?e,z?),RU,RL(-1,b?{<0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),2,n)
        + den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*S(R(?d,y,abs_(b)+2,?c),X(?e,z/2,2),n)*g(nargs_(?c))
        - S(R(?d,y+1,-1,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,-1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,-(y+2),b,?c),X(?e,z,1),n)*g(nargs_(?c));
id GG(R(?d,y?{<0}),X(?e,z?),RU,RL(-1,b?{<0},?c),1,n?) = TT(R(?d,y),X(?e,z),RU,RL(b,?c),2,n)
        + den(2)*GG(R(?d,y,1),X(?e,z/2,2),RU,RL(?c),abs_(b)+1,n)
        + den(2)*S(R(?d,y,abs_(b)+2,?c),X(?e,z/2,2),n)*g(nargs_(?c))
        - S(R(?d,-(abs_(y)+1),-1,b,?c),X(?e,z,1,1),n)*g(nargs_(?c))
        + den(2)*S(R(?d,y,1,-1,b,?c),X(?e,z/2,2,1,1),n)*g(nargs_(?c))
        - S(R(?d,y,-2,b,?c),X(?e,z/2,2,1),n)*g(nargs_(?c))
        + S(R(?d,abs_(y)+2,b,?c),X(?e,z,1),n)*g(nargs_(?c));
*--#]

*--#]

if ((match(once,GG(R(?e),X(?d),RU,RL(b?,?c),k?{>0},n?)))||(match(once,GG(R(?e),X(?b),RU(d?,?a),RL,k?{>0},n?)))||(match(once,TT(R(?e),X(?x),RU,RL(b?,?c),k?{>1},n?)))||(match(once,TT(R(?e),X(?x),RU(d?,?a),RL,k?{>1},n?))));
    redefine i "0";
endif;
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
.sort
#enddo
*--#]

*--#[ 0 S-sums
#write " The recursion for one S-sum is finished and the recursion for no S-sum now starts"
*
* These first 6 id statements are there to initiate the recursion if we encounter an inverse binomial sum containing no S-sums.
*

*--#[k=0

*--#[Sign altering
* k=0 (sommetjes equation 7.3)
id TT(R,X,RU,RL,0,n?) = -(1+sign(n))*den(n+2);
*--#]

*--#[Fixed sign
* k=0 (sommetjes equation 7.46)
id GG(R,X,RU,RL,0,n?) = -1 
        + (n+1)*S(R(1),X(2),n)*den(2)^(n+1);
*--#]

*--#]

*--#[k=1

*--#[Sign altering
* k=1 (sommetjes equation 7.2)
id TT(R,X,RU,RL,1,n?) = -(-1+sign(n))*den(n)*den(n+1)
        -den(n);
*--#]

*--#[Fixed sign
* k=1 (sommetjes equation 7.47)
id GG(R,X,RU,RL,1,n?) = -den(n) 
        + S(R(1),X(2),n)*den(2)^(n);
*--#]

*--#]

*--#[k>1

*--#[Sign altering
* k>1 (sommetjes equation 7.1)
id TT(R,X,RU,RL,k?{>1},n?) = - sign(n)*den(n)^k
        + 2*S(R(-k),X(1),n)
        + S(R(k),X(1),n)
        - sum_(jjj,2,k-1,TT(R(k-jjj),X(1),RU,RL,jjj,n));
*--#]

*--#[Fixed sign
* k>1 (sommetjes equation 7.48)
id GG(R,X,RU,RL,k?{>1},n?) = -den(n)^k 
        + S(R(k),X(1),n) 
        - sum_(jjj,2,k-1,GG(R(k-jjj),X(1),RU,RL,jjj,n))
        - 2*GG(R(k-1),X(1),RU,RL,1,n);
*--#]

*--#]

id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
.sort
*
* The zero S-sums recursion
*
#do i = 1,1

*--#[k=1

*--#[Fixed sign
* k=1 (sommetjes equation 7.47) Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?a,m?{>=0}),X(?b,c?),RU,RL,1,n?) = -S(R(?a,m+1),X(?b,c),n) 
        + S(R(?a,m,1),X(?b,c/2,2),n);
id GG(R(?a,m?{<0}),X(?b,c?),RU,RL,1,n?) = -S(R(?a,-(abs_(m)+1)),X(?b,c),n) 
        + S(R(?a,m,1),X(?b,c/2,2),n);
*--#]

*--#]
.sort
*--#[k>1

*--#[Sign altering
* k>1 (sommetjes equation 7.1). Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id TT(R(?a,m?{>=0}),X(?x,y?),RU,RL,k?{>1},n?) = - S(R(?a,-(m+k)),X(?x,y),n)
        + 2*S(R(?a,m,-k),X(?x,y,1),n)
        + S(R(?a,m,k),X(?x,y,1),n)
        - sum_(jjj,2,k-1,TT(R(?a,m,k-jjj),X(?x,y,1),RU,RL,jjj,n));
id TT(R(?a,m?{<0}),X(?x,y?),RU,RL,k?{>1},n?) = - S(R(?a,abs_(m)+k),X(?x,y),n)
        + 2*S(R(?a,m,-k),X(?x,y,1),n)
        + S(R(?a,m,k),X(?x,y,1),n)
        - sum_(jjj,2,k-1,TT(R(?a,m,k-jjj),X(?x,y,1),RU,RL,jjj,n));
*--#]

*--#[Fixed sign
* k>1 (sommetjes equation 7.48)Has two options to handle the first integer in the R-vector
* being either greater than or equal to zero or less than zero.
id GG(R(?a,m?{>=0}),X(?b,c?),RU,RL,k?{>1},n?) = -S(R(?a,m+k),X(?b,c),n)
        + S(R(?a,m,k),X(?b,c,1),n) 
        - sum_(jjj,2,k-1,GG(R(?a,m,k-jjj),X(?b,c,1),RU,RL,jjj,n))
        - 2*GG(R(?a,m,k-1),X(?b,c,1),RU,RL,1,n);
id GG(R(?a,m?{<0}),X(?b,c?),RU,RL,k?{>1},n?) = -S(R(?a,-(abs_(m)+k)),X(?b,c),n)
        + S(R(?a,m,k),X(?b,c,1),n) 
        - sum_(jjj,2,k-1,GG(R(?a,m,k-jjj),X(?b,c,1),RU,RL,jjj,n))
        - 2*GG(R(?a,m,k-1),X(?b,c,1),RU,RL,1,n);
*--#]

*--#]

if ((match(once,GG(R(?a,m?),X(?b,c?),RU,RL,k?{>0},n?)))||(match(once,TT(R(?e),X(?x),RU,RL,k?{>1},n?))));
    redefine i "0";
endif;
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
.sort
#enddo
*--#]

*--#[ Fixing the length of the X-vector in the S-sums
repeat id S(R(?a),X(?b),n?)*g(c?{>0}) = S(R(?a),X(?b,1),n)*g(c-1);
id g(0) = 1;
*--#]

*--#[ Special cases for the S-sums
id S(R,n?) = 1;
id S(R(?a),0) = 0;
id S(R,X,n?) = 1;
id S(R(?a),X(?b),0) = 0;
*--#]

*--#[ Solving the harmonic sums of the form S(R(?a),1)
#do i = 1,1
id S(R(a?{<0},?b),X(c?,?d),1) = -c*S(R(?b),X(?d),1);
id S(R(a?{>=0},?b),X(c?,?d),1) = c*S(R(?b),X(?d),1);
if (match(once,S(R(a?,?b),X(c?,?d),1)));
    redefine i "0";
endif;
.sort
#enddo
id S(R,X,1) = 1;
*--#]

*--#[ Resetting the Splitarg function for sums that contain the inverse binomial sum as a nested sub-sum
id den(?x,k?{>0}) = den(?x)^k;
repeat id den(a?,b?,?c) = den(a+b,?c);
repeat id S(R(?a),b?,c?,?d) = S(R(?a),b+c,?d);
.sort
*--#]

#endprocedure
*--#]

*--#[ Prepsync
#procedure Prepsync
*
* Procedure to synchronize the arguments of the harmonic sums appearing in the inverse binomial sum.
* 
Splitarg, S;
*
#do i = 1,1

*--#[ a>0
*
* The following 4 id statements are there to synchronize the arguments of the harmonic sums if their argument is greater than
* it is supposed to be.
*
id S(R(d?{>=0},?a),b?{>0},j1) = S(R(d,?a),0,j1) + sum_(jjj,1,b,den(j1+jjj)^(d)*S(R(?a),jjj,j1));
id S(R(d?{<0},?a),b?{>0},j1) = S(R(d,?a),0,j1) + sum_(jjj,1,b,sign(jjj+j1)*den(j1+jjj)^(abs_(d))*S(R(?a),jjj,j1));
id S(R(d?{>=0},?a),b?{>0},-j1,n) = S(R(d,?a),0,-j1,n) + sum_(jjj,1,b,den(n-j1+jjj)^(d)*S(R(?a),jjj,-j1,n));
id S(R(d?{<0},?a),b?{>0},-j1,n) = S(R(d,?a),0,-j1,n) + sum_(jjj,1,b,sign(jjj+n-j1)*den(n-j1+jjj)^(abs_(d))*S(R(?a),jjj,-j1,n));
*--#]

*--#[ a<0
*
* The following 4 id statements are there to synchronize the arguments of the harmonic sums if their argument is less than
* it is supposed to be.
*
id S(R(d?{>=0},?a),b?{<0},j1) = S(R(d,?a),b+1,j1) - S(R(?a),b+1,j1)*den(j1+b+1)^(d);
id S(R(d?{<0},?a),b?{<0},j1) = S(R(d,?a),b+1,j1) - sign(j1+b+1)*S(R(?a),b+1,j1)*den(j1+b+1)^(abs_(d));
id S(R(d?{>=0},?a),b?{<0},-j1,n) = S(R(d,?a),b+1,-j1,n) - S(R(?a),b+1,-j1,n)*den(n-j1+b+1)^(d);
id S(R(d?{<0},?a),b?{<0},-j1,n) = S(R(d,?a),b+1,-j1,n) - sign(n-j1+b+1)*S(R(?a),b+1,-j1,n)*den(n-j1+b+1)^(abs_(d));
*--#]

if ((match(once,S(R(d?,?a),b?{<0},j1)))||(match(once,S(R(d?,?a),b?{<0},-j1,n)))||(match(once,S(R(d?,?a),b?{>0},j1)))||(match(once,S(R(d?,?a),b?{>0},-j1,n))));
    redefine i "0";
endif;
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
.sort
#enddo
* Here we use the fact that the argument of the harmonic sums appearing in the inverse binomial sum is always greater than zero.
id S(R,?a) = 1;
* Rewriting the harmonic sums back into standard notation
id S(R(?a),d?int_,-j1,n) = S(R(?a),d+n-j1);
id S(R(?a),d?int_,j1) = S(R(?a),j1+d);
id S(R(?a),-j1,n) = S(R(?a),n-j1);
repeat id S(R(?a),b?,c?,?d) = S(R(?a),b+c,?d);
#endprocedure
*--#]

*--#[ Boundaryfix
#Procedure Boundaryfix
*
* Procedure to fix the sum boundaries of the inverse binomial sum
*
.sort
* First we rewrite the input into a format that can easily be recognized by FORM
Splitarg, sum, den, S;
id den(c?,-j) = (-1)*den(-c,j);
id den(c?,j) = den(c,j,1);
repeat id den(c?,j,m?{>0})*den(c?,j,n?{>0}) = den(c,j,m+n);
id den(-j) = (-1)*den(j);
id den(j) = den(j,1);
repeat id den(j,m?{>0})*den(j,n?{>0}) = den(j,m+n);
id den(c?int_,n) = den(n+c);
id den(c?int_,-n) = den(-n+c);
id S(R(?a),c?int_,n) = S(R(?a),n+c);
id S(R(?a),c?int_,-n) = S(R(?a),-n+c);

*--#[ Checks
* Here we check if the upper limit of the inverse binomial sum is too high
if ((match(once,sum(j,w?,x?{>0},n?)*invbino(n?,j)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(c?,j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(c?,j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(c?,j,k?{>-1})*sign(j)*S(R(?a),-j,n?)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(c?,j,k?{>-1})*S(R(?a),-j,n?)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?)*S(R(?b),j)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*S(R(?a),-j,n?)*S(R(?b),j)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?)))||
    (match(once,sum(j,w?,n?)*invbino(n?,j)*S(R(?a),-j,n?))));
    $check4 = 1;
endif;
.sort
#if ( '$check4' == 1 )
    #write "The upper limit of the inverse binomial sum is too high and the lower limit may be too low. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
* Here we check if the boundaries of the inverse binomial sum don't overlap each other
id sum(j,a?{>0},b?{>0}) = sum(j,a,b)*g(b-a);
if (match(once,g(x?{<0})));
    $check11 = 1;
endif;
.sort
#if ( '$check11' == 1 )
    #write "The limits of your inverse binomial sum overlap. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
id g(x?{>=0}) = 1;
* Here we check if the boundaries of the inverse binomial sum with an offset in the denominator are not too low
id sum(j,a?{>-1},b?{<0},n?)*den(c?{<0},j,k?) = sum(j,a,b,n)*den(c,j,k)*g(c+a);
id sum(j,a?{>-1},n?)*den(c?{<0},j,k?) = sum(j,a,n)*den(c,j,k)*g(c+a);
if (match(once,g(x?{<1})));
    $check98 = 1;
endif;
.sort
#if ( '$check98' == 1 )
    #write "The lower limit of your inverse binomial sum is too low, causing the inverse binomial sum to contain a division by zero. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
id g(x?{>=0}) = 1;
* We add a check to warn the user about having too low sum boundaries
if ((match(once,sum(j,0,a?,n?)*den(j,k?)))||
      (match(once,sum(j,0,a?,n?)*S(R(?a),j)))||
      (match(once,sum(j,0,n?)*den(j,k?)))||
      (match(once,sum(j,0,n?)*S(R(?a),j))));
    $check99 = 1;
endif;
.sort
#if ( '$check99' == 1 )
    #write "The lower limit of the inverse binomial sum is too low, causing the inverse binomial sum to contain either a division by zero or a harmonic sum evaluated at argument zero. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
* check for lower bound zero with den and S, add the possibility for zero if c>0 but check for S(j) and move checks to front
*--#]

*--#[ c>0
*
* Now we can start fixing the sum boundaries, first we have the id statements to fix the sum boundaries 
* of the inverse binomial sums with c>0
* 
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*den(n-1+c)^k*sign(n-1)*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*den(n-1+c)^k*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - den(n)*den(n-1+c)^k*sign(n-1)*S(R(?a),1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),n-j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj));
id sum(j,0,e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      + den(c)^k*S(R(?a),n);
id sum(j,0,-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      + den(c)^k*S(R(?a),n);
id sum(j,0,-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - den(n)*den(n-1+c)^k*sign(n-1)*S(R(?a),1)
      + den(c)^k*S(R(?a),n);
id sum(j,0,x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),n-j))
      + den(c)^k*S(R(?a),n);
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - den(n)*den(n-1+c)^k*S(R(?a),1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*S(R(?a),n-j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj));
id sum(j,0,e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj))*g(e-(n-1)) 
      + den(c)^k*S(R(?a),n);
id sum(j,0,-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      + den(c)^k*S(R(?a),n);
id sum(j,0,-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - den(n)*den(n-1+c)^k*S(R(?a),1)
      + den(c)^k*S(R(?a),n);
id sum(j,0,x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*S(R(?a),n-j))
      + den(c)^k*S(R(?a),n);
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      - den(n)*den(n-1+c)^k*sign(n-1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      + den(n+c)^k*sign(n)*S(R(?b),n)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      - den(n)*den(n-1+c)^k*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      + den(n+c)^k*S(R(?b),n)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - den(n)*den(n-1+c)^k*sign(n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      + den(n+c)^k*sign(n)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj));
id sum(j,0,e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g(e-(n-1)) 
      + den(c)^k;
id sum(j,0,-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      + den(c)^k;
id sum(j,0,-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - den(n)*den(n-1+c)^k*sign(n-1)
      + den(c)^k;
id sum(j,0,x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j))
      + den(c)^k;
id sum(j,0,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      + den(n+c)^k*sign(n)
      + den(c)^k;
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k)*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k);
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k);
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      - den(n)*den(n-1+c)^k
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k);
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k);
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      + den(n+c)^k
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj+c)^k);
id sum(j,0,e?{>0})*invbino(n?{>1},j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k)*g(e-(n-1)) 
      + den(c)^k;
id sum(j,0,-1,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      + den(c)^k;
id sum(j,0,-2,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      - den(n)*den(n-1+c)^k
      + den(c)^k;
id sum(j,0,x?{<-2},n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k)
      + den(c)^k;
id sum(j,0,n?)*invbino(n?,j)*den(c?{>0},j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j+c)^k
      + den(n+c)^k
      + den(c)^k;
*--#]

*--#[ c<0
*
* Next we have the id statements to fix the sum boundaries of the inverse binomial sums with c<0
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*den(n-1+c)^k*sign(n-1)*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*den(n-1+c)^k*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj)*S(R(?b),jj))*g1(w-(1-c));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj))*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj))*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - den(n)*den(n-1+c)^k*sign(n-1)*S(R(?a),1)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj))*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),n-j))
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?a),n-jj))*g1(w-(1-c));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*S(R(?a),n?{>1},-j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj))*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj))*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - den(n)*den(n-1+c)^k*S(R(?a),1)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj))*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*S(R(?a),n-j))
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?a),n-jj))*g1(w-(1-c));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      - den(n)*den(n-1+c)^k*sign(n-1)*S(R(?b),n-1)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j)*S(R(?b),j))
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)*S(R(?b),j)
      + den(n+c)^k*sign(n)*S(R(?b),n)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj)*S(R(?b),jj))*g1(w-(1-c));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      - den(n)*den(n-1+c)^k*S(R(?b),n-1)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*S(R(?b),j))
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj))*g1(w-(1-c));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*S(R(?b),j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*S(R(?b),j)
      + den(n+c)^k*S(R(?b),n)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*S(R(?b),jj))*g1(w-(1-c));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1})*sign(j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - den(n)*den(n-1+c)^k*sign(n-1)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k*sign(j))
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g1(w-(1-c));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1})*sign(j) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k*sign(j)
      + den(n+c)^k*sign(n)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k*sign(jj))*g1(w-(1-c));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(c?{<0},j,k?{>-1}) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj+c)^k)*g(e-(n-1)) 
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k)*g1(w-(1-c));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1}) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k)*g1(w-(1-c));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1}) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k
      - den(n)*den(n-1+c)^k
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k)*g1(w-(1-c));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1}) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j+c)^k)
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k)*g1(w-(1-c));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(c?{<0},j,k?{>-1}) = sum(j,1-c,n-1)*invbino(n,j,0)*den(j+c)^k
      + den(n+c)^k
      - sum_(jj,1-c,w-1,invbino(n,jj)*den(jj+c)^k)*g1(w-(1-c));
*--#]

*--#[ c=0
*
* Next we have the id statements to fix the sum boundaries of the inverse binomial sums with c=0
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*den(n-1)^k*sign(n-1)*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k*sign(j)*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1})*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*den(n-1)^k*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1})*sign(j)*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)
      - den(n)*den(n-1)^k*sign(n-1)*S(R(?a),1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k*sign(j)*S(R(?a),n-j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?a),n-jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1})*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)
      - den(n)*den(n-1)^k*S(R(?a),1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k*S(R(?a),n-j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?a),n-jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?b),j)
      - den(n)*den(n-1)^k*sign(n-1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k*sign(j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)*S(R(?b),j)
      + den(n)^k*sign(n)*S(R(?b),n)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?b),j)
      - den(n)*den(n-1)^k*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?b),jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(j,k?{>-1})*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*S(R(?b),j)
      + den(n)^k*S(R(?b),n)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k*sign(jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)
      - den(n)*den(n-1)^k*sign(n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k*sign(j))
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*den(j,k?{>-1})*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k*sign(j)
      + den(n)^k*sign(n)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k*sign(jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*den(j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*den(jj)^k)*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k);
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*den(j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k);
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*den(j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k
      - den(n)*den(n-1)^k
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k);
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*den(j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k
      - sum(j,n+x+1,n-1,invbino(n,j)*den(j)^k)
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k);
id sum(j,w?{>0},n?)*invbino(n?,j)*den(j,k?{>-1}) = sum(j,1,n-1)*invbino(n,j,0)*den(j)^k
      + den(n)^k
      - sum_(jj,1,w-1,invbino(n,jj)*den(jj)^k);
*--#]

*--#[ k=0
*
* Next we have the id statements to fix the sum boundaries of the inverse binomial sums with k=0
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*sign(j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*sign(n-1)*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*sign(j)*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*S(R(?a),n?{>1},-j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*S(R(?a),n-jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)*S(R(?b),j)
      - den(n)*S(R(?a),1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*S(R(?a),n-j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*sign(j)*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      - den(n)*sign(n-1)*S(R(?a),1)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*sign(j)*S(R(?a),n-j))
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj));
id sum(j,0,e?{>0})*invbino(n?{>1},j)*sign(j)*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*sign(jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      + S(R(?a),n);
id sum(j,0,-1,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      + S(R(?a),n);
id sum(j,0,-2,n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      - den(n)*sign(n-1)*S(R(?a),1)
      + S(R(?a),n);
id sum(j,0,x?{<-2},n?)*invbino(n?,j)*sign(j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*sign(j)*S(R(?a),n-j))
      + S(R(?a),n);
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      - den(n)*S(R(?a),1)
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*S(R(?a),n-j))
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?a),n-jj));
id sum(j,0,e?{>0})*invbino(n?{>1},j)*S(R(?a),n?{>1},-j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*S(R(?a),n-jj))*g(e-(n-1)) 
      + S(R(?a),n);
id sum(j,0,-1,n?)*invbino(n?,j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      + S(R(?a),n);
id sum(j,0,-2,n?)*invbino(n?,j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      - den(n)*S(R(?a),1)
      + S(R(?a),n);
id sum(j,0,x?{<-2},n?)*invbino(n?,j)*S(R(?a),-j,n?) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?a),n-j)
      - sum(j,n+x+1,n-1,invbino(n,j)*S(R(?a),n-j))
      + S(R(?a),n);
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*sign(jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?b),j)
      - den(n)*sign(n-1)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*sign(j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?b),jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*sign(j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)*S(R(?b),j)
      + sign(n)*S(R(?b),n)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?b),j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*S(R(?b),jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?b),jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?b),j)
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?b),jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?b),j)
      - den(n)*S(R(?b),n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?b),jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?b),j)
      - sum(j,n+x+1,n-1,invbino(n,j)*S(R(?b),j))
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?b),jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*S(R(?b),j) = sum(j,1,n-1)*invbino(n,j,0)*S(R(?b),j)
      + S(R(?b),n)
      - sum_(jj,1,w-1,invbino(n,jj)*S(R(?b),jj));
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*sign(jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      - den(n)*sign(n-1)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      - sum(j,n+x+1,n-1,invbino(n,j)*sign(j))
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj));
id sum(j,w?{>0},n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      + sign(n)
      - sum_(jj,1,w-1,invbino(n,jj)*sign(jj));
id sum(j,0,e?{>0})*invbino(n?{>1},j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj)*sign(jj))*g(e-(n-1)) 
      + 1;
id sum(j,0,-1,n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      + 1;
id sum(j,0,-2,n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      - den(n)*sign(n-1)
      + 1;
id sum(j,0,x?{<-2},n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      - sum(j,n+x+1,n-1,invbino(n,j)*sign(j))
      + 1;
id sum(j,0,n?)*invbino(n?,j)*sign(j) = sum(j,1,n-1)*invbino(n,j,0)*sign(j)
      + sign(n)
      + 1;
*
id sum(j,w?{>0},e?{>0})*invbino(n?{>1},j) = sum(j,1,n-1)*invbino(n,j,0)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj))*g(e-(n-1)) 
      - sum_(jj,1,w-1,invbino(n,jj));
id sum(j,w?{>0},-1,n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      - sum_(jj,1,w-1,invbino(n,jj));
id sum(j,w?{>0},-2,n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      - den(n)
      - sum_(jj,1,w-1,invbino(n,jj));
id sum(j,w?{>0},x?{<-2},n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      - sum(j,n+x+1,n-1,invbino(n,j))
      - sum_(jj,1,w-1,invbino(n,jj));
id sum(j,w?{>0},n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      + 1
      - sum_(jj,1,w-1,invbino(n,jj));
id sum(j,0,e?{>0})*invbino(n?{>1},j) = sum(j,1,n-1)*invbino(n,j,0)
      + sig_(e-(n-1))*sum(jj,e,n-1,invbino(n,jj))*g(e-(n-1)) 
      + 1;
id sum(j,0,-1,n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      + 1;
id sum(j,0,-2,n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      - den(n)
      + 1;
id sum(j,0,x?{<-2},n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      - sum(j,n+x+1,n-1,invbino(n,j))
      + 1;
id sum(j,0,n?)*invbino(n?,j) = sum(j,1,n-1)*invbino(n,j,0)
      + 1
      + 1;
*--#]

*--#[ Notation
*
* We now fix the notation of some of the sums and get rid of internal checks
*
.sort
id sum(jj,e?int_,n?int_,?a)*g(x?{<0}) = sum_(jj,e+1,n,?a);
id sum(jj,e?int_,n?int_,?a)*g(1) = sum_(jj,n+1,e,?a);
id S(R(?a),n?{<1}) = 0;
id g(0) = 0;
id g1(a?{>=0}) = 1;
.sort
*--#]

*--#[ Checks
*
* We add a check to warn the user about having too low sum boundaries
*
if ((match(once,sum(j,w?{<0},a?,n?)))||(match(once,g1(a?{<0}))));
    $check5 = 1;
endif;
.sort
#if ( '$check5' == 1 )
    #write "The lower limit of the inverse binomial sum is too low. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif

* Here we check if the upper limit of the inverse binomial sum is too high
if (match(once,g(x?{>1})));
    $check9 = 1;
endif;
.sort
#if ( '$check9' == 1 )
    #write "The upper limit of the inverse binomial sum is too high and the lower limit may be too low. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif

if ( match(once,invbino(n,j)) );
    $check6 = 1;
endif;
.sort
#if ( '$check6' == 1 )
    #write "The limits of the inverse binomial sum are incorrect. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
*--#]

id invbino(n?,j?,0) = invbino(n,j);
id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
id invbino(n?int_,j?int_) = 1/binom_(n,j);
id den(?x,k?{>0}) = den(?x)^k;
repeat id den(a?,b?,?c) = den(a+b,?c);
repeat id S(R(?a),b?,c?,?d) = S(R(?a),b+c,?d);
.sort
#endprocedure
*--#]

*--#[ Denflip
#Procedure Denflip
*
* Procedure to rewrite an inverse binomial sum with n-j as its denominator into an inverse binomial sum with j as its denominator
*
.sort
* First we rewrite the input into a format that can easily be recognized by FORM
Splitarg, den, sum, S;
id den(c?,j,-n) = (-1)*den(-c,-j,n);
id den(c?,-j,n) = den(c,-j,n,1);
repeat id den(c?,-j,n,m?{>0})*den(c?,-j,n,x?{>0}) = den(c,-j,n,m+x);
id den(j,-n) = (-1)*den(-j,n);
id den(-j,n) = den(-j,n,1);
repeat id den(-j,n,m?{>0})*den(-j,n,x?{>0}) = den(-j,n,m+x);
id den(c?,-j) = (-1)*den(-c,j);
id den(c?,j) = den(c,j,1);
repeat id den(c?,j,m?{>0})*den(c?,j,n?{>0}) = den(c,j,m+n);
id den(-j) = (-1)*den(j);
id den(j) = den(j,1);
repeat id den(j,m?{>0})*den(j,n?{>0}) = den(j,m+n);
id den(c?int_,n) = den(n+c);
id den(c?int_,-n) = den(-n+c);
id S(R(?a),c?int_,n) = S(R(?a),n+c);
id S(R(?a),c?int_,-n) = S(R(?a),-n+c);

*--#[ Check
* Here we check if the upper limit of the inverse binomial sum is too high
if ((match(once,sum(j,w?,x?{>0},n)*invbino(n,j)*den(c?int_,-j,n,k?{>0})))||
    (match(once,sum(j,w?,n)*invbino(n,j)*den(-j,n,k?{>0})))||
    (match(once,sum(j,w?,x?{>0},n)*invbino(n,j)*den(-j,n,k?{>0})))||
    (match(once,sum(j,w?,n)*invbino(n,j)*den(c?int_,-j,n,k?{>0}))));
    $check7 = 1;
endif;
.sort
#if ( '$check7' == 1 )
    #write "The upper limit of the inverse binomial sum is too high. Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
*--#]

*--#[ c not equal to zero
*
* Now we can start rewriting the inverse binomial sums with n-j as  its denominator into an inverse binomial sum with j as its denominator.
* First we have the id statements of the inverse binomial sums with c not equal to zero.
* 
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1})*sign(j)*S(R(?a),-j,n)*S(R(?b),j) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),j)*S(R(?b),n-j);
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1})*S(R(?a),-j,n)*S(R(?b),j) = sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k*S(R(?a),j)*S(R(?b),n-j);
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1})*sign(j)*S(R(?a),-j,n) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),j);
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1})*S(R(?a),-j,n) = sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k*S(R(?a),j);
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1})*sign(j)*S(R(?a),j) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k*sign(j)*S(R(?a),n-j);
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1})*S(R(?a),j) = sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k*S(R(?a),n-j);
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1})*sign(j) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k*sign(j);
id sum(j,w?{>0},x?{<0},n)*invbino(n,j)*den(c?,-j,n,k?{>-1}) = sum(j,-x,n-w)*invbino(n,j)*den(j+c)^k;
*--#]

*--#[ c=0
*
* Next we have the id statements to fix the sum boundaries of the inverse binomial sums with c=0
*
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1})*sign(j)*S(R(?a),-j,n)*S(R(?b),j) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j)^k*sign(j)*S(R(?a),j)*S(R(?b),n-j);
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1})*S(R(?a),-j,n?)*S(R(?b),j) = sum(j,-x,n-w)*invbino(n,j)*den(j)^k*S(R(?a),j)*S(R(?b),n-j);
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1})*sign(j)*S(R(?a),-j,n) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j)^k*sign(j)*S(R(?a),j);
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1})*S(R(?a),-j,n) = sum(j,-x,n-w)*invbino(n,j)*den(j)^k*S(R(?a),j);
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1})*sign(j)*S(R(?a),j) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j)^k*sign(j)*S(R(?a),n-j);
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1})*S(R(?a),j) = sum(j,-x,n-w)*invbino(n,j)*den(j)^k*S(R(?a),n-j);
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1})*sign(j) = sign(n)*sum(j,-x,n-w)*invbino(n,j)*den(j)^k*sign(j);
id sum(j,w?{>-1},x?{<0},n)*invbino(n,j)*den(-j,n,k?{>-1}) = sum(j,-x,n-w)*invbino(n,j)*den(j)^k;
*--#]

*--#[ Notation and checks
*
* We now fix the notation of some of the sums and get rid of internal checks
*
id sum(j,w?,x?,n?)*den(c?,j,k?{>-1}) = sum(j,w,n+x)*den(j+c)^k;
id sum(j,w?,x?,n?)*den(j,k?{>-1}) = sum(j,w,n+x)*den(j)^k;
id sum(j,w?,x?,n?)*invbino(n,j) = sum(j,w,n+x)*invbino(n,j);
id S(R(?a),-j,n) = S(R(?a),n-j);
id S(R(?a),n?int_,-j) = S(R(?a),n-j);
*
* We add a check to warn the user about not having been able to rewrite the inverse binomial sum into a sum with the correct denominator
*
if ((match(once,den(c?,-j,n,k?)))||(match(once,den(-j,n,k?))));
    $check8 = 1;
endif;
.sort
#if ( '$check8' == 1 )
    #write "The procedure has not managed to rewrite the inverse binomial sum into a sum with the correct denominator.
    This is probably due to the fact that the lower limit of the inverse binomial sum is too low.
    Please see the manual for instructions on how to write down your inverse binomial sum as input."
    #terminate
#endif
*--#]

id sign(n?int_) = sign_(n);
id den(n?int_) = 1/n;
id invbino(n?int_,j?int_) = 1/binom_(n,j);
id den(?x,k?{>0}) = den(?x)^k;
repeat id den(a?,b?,?c) = den(a+b,?c);
repeat id S(R(?a),b?,c?,?d) = S(R(?a),b+c,?d);
.sort
#endprocedure
*--#]

*--#[ IBIS
#procedure IBIS

#call Interface

#call invbino

#endprocedure
*--#]

*--#]