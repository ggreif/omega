
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PRIMITIVE BLOCKS

vardef circle(expr c, r, s) = 
  begingroup
  save p;
  path p;
  p = (c+(0,-r))..(c+(-r,0))..(c+(0,r))..(c+(r,0))..cycle;
  draw p;
  label(s,c);
  p
  endgroup
enddef;

vardef nil(expr c, r) = 
  begingroup
  save p;
  path p;
  p = (c-(0,r))..(c-(r,0))..(c+(0,r))..(c+(r,0))..cycle;
  draw p;
  draw (c+(r,r))..c cutbefore p;
  draw (c..c-(r,r)) cutafter p;
  draw (c+(-r,r))..c cutbefore p;
  draw (c..c+(r,-r)) cutafter p;
  p
  endgroup
enddef;

vardef skip(expr c, r) = 
  begingroup
  save p;
  path p;
  p = (c-(0,r))..(c-(r,0))..(c+(0,r))..(c+(r,0))..cycle;
  draw p;
  draw (c+(r,r))..c cutbefore p;
  draw (c..c-(r,r)) cutafter p;
  p
  endgroup
enddef;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Global constants

numeric s;
s = 15;

color blockcolor;
blockcolor = .9 white;

beginfig(1);
pair a,b,c,d,e,f,g;
path x,y,z,u,v,w,t;
numeric r;
numeric l;
l = 20;
r = 5;
a = (100,100);
a - b = (0,l);
c - d = (0,l);
b - c = (l,0);

x = circle(a,r,"2");
y = circle(b,r,"3");
draw a--b cutafter y cutbefore x;

u = circle(c,r,"4");
v = circle(d,r,"5");
draw c--d cutafter v cutbefore u;

draw a--c cutafter u cutbefore x;

g - a = 2*(l,0);
a - f = 2*(l,0);
f - e = 2*(l,0);
%t = nil (g,r);
w = skip(f,r);
z = circle(e,r,"1");
%drawarrow a--g cutafter t cutbefore x;
drawarrow f--a cutafter x cutbefore w;
drawarrow e--f cutafter w cutbefore z;
endfig;

end;

Skip
Skip
Cons (Tree 2 (ConsF (Tree 4 (ConsF (Tree 5 NilF) NilF)) (ConsF (Tree 3 NilF) NilF))) 
Skip
Cons (Tree 0 (ConsF (Tree 11 (ConsF (Tree 16 (ConsF (Tree 17 (ConsF (Tree 18 NilF) NilF))
                                             (ConsF (Tree 19 NilF) NilF)))
                             (ConsF (Tree 12 (ConsF (Tree 13 NilF) NilF))
			     (ConsF (Tree 14 NilF)
			     NilF)))) 
             (ConsF (Tree 1 (ConsF (Tree 6 (ConsF (Tree 7 NilF) NilF))
                            (ConsF (Tree 9 NilF)
			    NilF)))
	     (ConsF (Tree 10 (ConsF (Tree 15 NilF) NilF))
	     (ConsF (Tree 8 NilF)
	     NilF)))))
Nil


%def machine(expr scale, p, l) =
%  begingroup
%  save A,B,C,D,E,F,L;
%  pair A,B,C,D,E,F;
%  %drawing commands...
%  C = p;
%  D-C = (scale,0);
%  B-A = F-E = .5(scale,0);
%  C-B = D-E = (0,scale);
%  fill B--C--D--E--cycle withcolor blockcolor;
%  draw A--B--C--D--E--F;
%  pair L;
%  L = .5[C,E];
%  label(l,L);
%  endgroup
%enddef;
%
%%%%% special pipe thing
%def compilerPipe(expr scale, fst, snd) =
%  snd = fst + (3,0)*scale;
%enddef;
%
%%%%% later
%def nameCompiler(expr scale,P,txt) =
%  label(txt,P+(scale,scale)/2);
%enddef;
