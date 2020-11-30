#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <math.h>

#define SMAX 1000 // maximum size

double *x,*xA,*xB,*xR,**y,**yA,**yB,**yR,***z,***zA,***zB,***zR;
int ***in,***out;
int steps,size,inputs,states,iterstride;
double eta,zeta,beta;
char statsfile[50],solfile[50],errfile[50],rulefile[50];


static inline double sq(double diff)
  {
  return diff*diff;
  }


static inline int sgnmod(int i)
  {
  return (i+size)%size;
  }
  
	
void ruleproj(int outnode,int *edge,double *xo,double *yo,double *zo,double *xp,double *yp,double *zp)
	{
	int s,smin,s1,s2,i,b[SMAX];
	double dist,distmin,d0,d1;
	
	distmin=1e10;
	
	for(s=0;s<states;++s)
		{
		s1=s;
		for(i=inputs;i>0;--i)
			{
			s2=s1/2;
			b[i-1]=s1-2*s2;
			s1=s2;
			}
			
		dist=0.;
		
		for(i=0;i<inputs;++i)
			dist+=sq(xo[edge[i]]-b[i]);
			
		if(outnode)
			dist+=(*yo==0.) ? sq(zo[s]) : sq(zo[s]-zeta);
		else
			{
			d0=sq(*yo)+sq(zo[s]);
			d1=sq(*yo-eta)+sq(zo[s]-zeta);
		
			dist+=(d0<d1) ? d0 : d1;
			}
		
		if(dist<distmin)
			{
			distmin=dist;
			smin=s;
			}
		}
			
	for(s=0;s<states;++s)
		zp[s]=zo[s];
		
	s1=smin;
	for(i=inputs;i>0;--i)
		{
		s2=s1/2;
		b[i-1]=s1-2*s2;
		s1=s2;
		}
		
	for(i=0;i<inputs;++i)
		xp[edge[i]]=b[i];
		
	if(outnode)
		{
		*yp=*yo;
		zp[smin]=(*yo==0.) ? 0. : zeta;
		}
	else
		{
		d0=sq(*yo)+sq(zo[smin]);
		d1=sq(*yo-eta)+sq(zo[smin]-zeta);
	
		if(d0<d1)
			{
			*yp=0.;
			zp[smin]=0.;
			}
		else
			{
			*yp=eta;
			zp[smin]=zeta;
			}
		}
	}
	
	
void outconcur(int innode,int *edge,double *xo,double *yo,double *xp,double *yp)
	{
	double c;
	int i;
	
	if(innode)
		{
		*yp=*yo;
		
		for(i=0;i<inputs;++i)
			xp[edge[i]]=(*yo)/eta;
		}
	else
		{
		c=eta*(*yo);
	
		for(i=0;i<inputs;++i)
			c+=xo[edge[i]];
			
		c/=eta+inputs/eta;
		
		*yp=c;
		
		c/=eta;
	
		for(i=0;i<inputs;++i)
			xp[edge[i]]=c;
		}
	}
	
	
void ruleconcur(double ***zo,double ***zp)
	{
	int s,l,p;
	double c;
	
	for(s=0;s<states;++s)
		{
		c=0.;
		for(l=1;l<=steps;++l)
		for(p=0;p<size;++p)
			c+=zo[l][p][s];
			
		c/=steps*size;
		
		for(l=1;l<=steps;++l)
		for(p=0;p<size;++p)
			zp[l][p][s]=c;
		}
	}


void projA(double *xo,double **yo,double ***zo)
	{
	int p,l;
	
	for(p=0;p<size;++p)
	for(l=1;l<=steps;++l)
		ruleproj(l==steps,in[l][p],xo,&yo[l][p],zo[l][p],xA,&yA[l][p],zA[l][p]);
	}
	

void projB(double *xo,double **yo,double ***zo)
	{
	int p,l;
	
	for(p=0;p<size;++p)
	for(l=0;l<steps;++l)
		outconcur(l==0,out[l][p],xo,&yo[l][p],xB,&yB[l][p]);
	
	ruleconcur(zo,zB);
	}
	
	
void ref(double *xo,double **yo,double ***zo)
	{
	int l,p,i,s;
	
	for(l=1;l<=steps;++l)
	for(p=0;p<size;++p)
		{
		for(i=0;i<inputs;++i)
			xR[in[l][p][i]]=2.*xo[in[l][p][i]]-x[in[l][p][i]];
			
		if(l<steps)
			yR[l][p]=2.*yo[l][p]-y[l][p];
		
		for(s=0;s<states;++s)
			zR[l][p][s]=2.*zo[l][p][s]-z[l][p][s];
		}
	}
	
	
double RRR()
	{
	int l,p,i,s;
	double err,diff;
	
	if(beta>0.)
		{
		projA(x,y,z);
		ref(xA,yA,zA);
		projB(xR,yR,zR);
		}
	else
		{
		projB(x,y,z);
		ref(xB,yB,zB);
		projA(xR,yR,zR);
		}
		
	err=0.;
	for(l=1;l<=steps;++l)
	for(p=0;p<size;++p)
		{
		for(i=0;i<inputs;++i)
			{
			diff=xB[in[l][p][i]]-xA[in[l][p][i]];
			x[in[l][p][i]]+=beta*diff;
			err+=diff*diff;
			}
			
		if(l<steps)
			{
			diff=yB[l][p]-yA[l][p];
			y[l][p]+=beta*diff;
			err+=diff*diff;
			}
		
		for(s=0;s<states;++s)
			{
			diff=zB[l][p][s]-zA[l][p][s];
			z[l][p][s]+=beta*diff;
			err+=diff*diff;
			}
		}
		
	return sqrt(err/(steps*size));
	}
	
  
void setup()
	{
	int edges,l,p,i,q;
	
	x=malloc(steps*size*inputs*sizeof(double));
	xA=malloc(steps*size*inputs*sizeof(double));
	xB=malloc(steps*size*inputs*sizeof(double));
	xR=malloc(steps*size*inputs*sizeof(double));
	
	in=malloc((steps+1)*sizeof(int**));
	out=malloc((steps+1)*sizeof(int**));
	
	for(l=0;l<=steps;++l)
		{
		in[l]=malloc(size*sizeof(int*));
		out[l]=malloc(size*sizeof(int*));
		
		for(p=0;p<size;++p)
			{
			in[l][p]=malloc(inputs*sizeof(int));
			out[l][p]=malloc(inputs*sizeof(int));
			}
		}
	
	edges=0;
	for(l=1;l<=steps;++l)
	for(p=0;p<size;++p)
		{
		for(i=0;i<inputs;++i)
			{
			q=sgnmod(p+i);
			
			in[l][p][i]=edges;
			out[l-1][q][i]=edges;
			
			++edges;
			}
		}
	
	y=malloc((steps+1)*sizeof(double*));
	yA=malloc((steps+1)*sizeof(double*));
	yB=malloc((steps+1)*sizeof(double*));
	yR=malloc((steps+1)*sizeof(double*));
	
	for(l=0;l<=steps;++l)
		{
		y[l]=malloc(size*sizeof(double));
		yA[l]=malloc(size*sizeof(double));
		yB[l]=malloc(size*sizeof(double));
		yR[l]=malloc(size*sizeof(double));
		}
	
	z=malloc((steps+1)*sizeof(double**));
	zA=malloc((steps+1)*sizeof(double**));
	zB=malloc((steps+1)*sizeof(double**));
	zR=malloc((steps+1)*sizeof(double**));
	
	for(l=0;l<=steps;++l)
		{
		z[l]=malloc(size*sizeof(double*));
		zA[l]=malloc(size*sizeof(double*));
		zB[l]=malloc(size*sizeof(double*));
		zR[l]=malloc(size*sizeof(double*));
		
		for(p=0;p<size;++p)
			{
			z[l][p]=malloc(states*sizeof(double));
			zA[l][p]=malloc(states*sizeof(double));
			zB[l][p]=malloc(states*sizeof(double));
			zR[l][p]=malloc(states*sizeof(double));
			}
		}
	}
	
	
int getdata(char *datafile)
	{
	FILE *fp;
	int l,p;
	char data[SMAX];
	
	fp=fopen(datafile,"r");
	if(!fp)
		{
		printf("cannot open datafile\n");
		return 0;
		}
	
	fgets(data,SMAX,fp);
	
	size=strlen(data)-1;
	
	setup();
	
	l=0;
	for(p=0;p<size;++p)
		{
		y[l][p]=eta*(data[p]-'0');
		yA[l][p]=y[l][p];
		yB[l][p]=y[l][p];
		yR[l][p]=y[l][p];
		}
	
	fgets(data,SMAX,fp);
	
	l=steps;
	for(p=0;p<size;++p)
		{
		y[l][p]=eta*(data[p]-'0');
		yA[l][p]=y[l][p];
		yB[l][p]=y[l][p];
		yR[l][p]=y[l][p];
		}
		
	fclose(fp);
	
	return 1;
	}
	

double urand()
  {
  return ((double)rand())/RAND_MAX;
  }
  
  
void randstart()
	{
	int l,p,i,s;
	
	for(l=1;l<=steps;++l)
	for(p=0;p<size;++p)
		{
		for(i=0;i<inputs;++i)
			x[in[l][p][i]]=urand();
			
		if(l<steps)
			y[l][p]=eta*urand();
		
		for(s=0;s<states;++s)
			z[l][p][s]=zeta*urand();
		}
	}
	
	
void printrule(FILE *fp)
	{
	int s;
	
	for(s=0;s<states;++s)
		fprintf(fp,"%3d",(int)(10.*zB[1][0][s]/zeta+10.5)-10);
		
	fprintf(fp,"\n");
	}
	
	
void printsol()
	{
	FILE *fp;
	int s;
	
	fp=fopen(solfile,"a");
	
	for(s=0;s<states;++s)
		fprintf(fp,"%1d",(int)(zB[1][0][s]/zeta+.5));
		
	fprintf(fp,"\n");
	
	fclose(fp);
	}
	
	
int solve(int maxiter,double stoperr)
	{
	int iter;
	double err;
	FILE *fp1,*fp2;
	
	fp1=fopen(rulefile,"w");
	fp2=fopen(errfile,"w");
	
	for(iter=1;iter<=maxiter;++iter)
		{
		err=RRR();
		
		if(iter%iterstride==0)
			{
			printrule(fp1);
			
			fprintf(fp2,"%10.6lf\n",err);
			}
		
		if(err<stoperr)
			{
			printrule(fp1);
			
			fprintf(fp2,"%10.6lf\n",err);
			
			fclose(fp1);
			fclose(fp2);
			
			return iter;
			}
		}
			
	fclose(fp1);
	fclose(fp2);
			
	return 0;
	}
	
	
int main(int argc,char* argv[])
	{
	char *datafile,*id;
	int iter,maxiter,trials,t,c,solcount;
	double stoperr,aveiter,elapsed,iterpersec;
	FILE *fp;
	clock_t start;
	
	if(argc==12)
		{
		datafile=argv[1];
		inputs=atoi(argv[2]);
		steps=atoi(argv[3]);
		eta=atof(argv[4]);
		zeta=atof(argv[5]);
		beta=atof(argv[6]);
		maxiter=atoi(argv[7]);
		iterstride=atoi(argv[8]);
		stoperr=atof(argv[9]);
		trials=atoi(argv[10]);
		id=argv[11];
		}
	else
		{
		printf("expected eleven arguments: datafile, inputs, steps, eta, zeta, beta, maxiter, iterstride, stoperr, trials, id\n");
		return 1;
		}
	
	sprintf(statsfile,"%s.stats",id);
	sprintf(solfile,"%s.sol",id);
	sprintf(errfile,"%s.err",id);
	sprintf(rulefile,"%s.rule",id);
	
	states=1<<inputs;
	
	if(!getdata(datafile))
		return 1;
	
	srand(time(NULL));
	start=clock();
	
	fp=fopen(solfile,"w");
	fclose(fp);
	
	fp=fopen(statsfile,"w");
	
	for(c=0;c<argc;++c)
    	fprintf(fp,"%s ",argv[c]);
    fprintf(fp,"\n\n");
	
	fclose(fp);
	
	solcount=0;
	aveiter=0.;
	for(t=1;t<=trials;++t)
		{
		randstart();
		
		iter=solve(maxiter,stoperr);
		
		if(iter)
			{
			++solcount;
			aveiter+=iter;
			
			printsol();
			}
		else
			aveiter+=maxiter;
		
		fp=fopen(statsfile,"a");
		fprintf(fp,"%3d%12d\n",t,iter);
		fclose(fp);
		}
		
	elapsed=((double)(clock()-start))/CLOCKS_PER_SEC;
	iterpersec=aveiter/elapsed;
	
	aveiter/=solcount;
	
	fp=fopen(statsfile,"a");
	fprintf(fp,"\n %d/%d solutions%10.2e iterations/solution\n",solcount,trials,aveiter);
	fprintf(fp,"%9.2e iterations/sec\n",iterpersec);
	fclose(fp);
	
	return 0;
	}