#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <math.h>

#define D 1 // distance to mask center
#define W 3 // width of mask
#define W2 9 // area of mask

#define SMAX 1000 // maximum size

double *w1,*w1A,*w1B,*w1R,*w2,*w2A,*w2B,*w2R;
double *x1,*x1A,*x1B,*x1R,*x2,*x2A,*x2B,*x2R;
double **y,**yA,**yB,**yR;

double *dflip;

int ***in,***out;

int steps,size,space,b1,b2;

double omega1,omega2,eta,beta;

char errfile[50],paramfile[50],statsfile[50],solfile[50];


static inline double sq(double diff)
	{
	return diff*diff;
	}


static inline int sgnmod(int i)
	{
	return (i+size)%size;
	}
	
	
double wxproj(double omega,int *edge,double *wo,double *xo,double *wn,double *xn,double *wf,double *xf,int *s,double *d)
	{
	int i,e;
	double dwxn,dw,dx;
	
	for(i=0;i<W2;++i)
		{
		e=edge[i];
		
		if(wo[e]<0.)
			{
			wn[i]=-.5*omega;
			wf[i]=.5*omega;
			
			d[i]=-2.*omega*wo[e];
			
			if(xo[e]<0.)
				{
				xn[i]=-.5;
				xf[i]=.5;
				
				d[i]+=-2.*xo[e];
				}
			else
				{
				xn[i]=.5;
				xf[i]=.5;
				}
			
			s[i]=0;
			}
		else 
			{
			wn[i]=.5*omega;
			
			if(xo[e]<0.)
				{
				xn[i]=-.5;
				xf[i]=.5;
				wf[i]=.5*omega;
				
				d[i]=-2.*xo[e];
				
				s[i]=0;
				}
			else
				{
				xn[i]=.5;
				
				dw=2.*omega*wo[e];
				dx=2.*xo[e];
				if(dw<dx)
					{
					xf[i]=.5;
					wf[i]=-.5*omega;
					
					d[i]=dw;
					}
				else
					{
					xf[i]=-.5;
					wf[i]=.5*omega;
					
					d[i]=dx;
					}
				
				s[i]=1;
				}
			}
		}
		
	dwxn=0.;
	for(i=0;i<W2;++i)
		{
		e=edge[i];
		dwxn+=sq(wn[i]-wo[e])+sq(xn[i]-xo[e]);
		}
		
	return dwxn;
	}
	
	
int flipcompare(const void *a,const void *b)
	{
	return dflip[*(int*)a] > dflip[*(int*)b];
	}


double aboveproj(int num,double dwxn,double *wn,double *xn,double *wf,double *xf,int *s,double *d,double *wa,double *xa)
	{
	double da;
	int i,j,r[W2],zeros;
	
	for(i=0;i<W2;++i)
		{
		wa[i]=wn[i];
		xa[i]=xn[i];
		}
		
	zeros=0;
	for(i=0;i<W2;++i)
		if(s[i]==0)
			r[zeros++]=i;
	
	dflip=d;
	
	qsort(r,zeros,sizeof(int),flipcompare);
	
	da=dwxn;
	for(j=0;j<num;++j)
		{
		da+=d[r[j]];
		
		wa[r[j]]=wf[r[j]];
		xa[r[j]]=xf[r[j]];
		}
	
	return da;
	}
	
	
double belowproj(int num,double dwxn,double *wn,double *xn,double *wf,double *xf,int *s,double *d,double *wb,double *xb)
	{
	double db;
	int i,j,r[W2],ones;
	
	for(i=0;i<W2;++i)
		{
		wb[i]=wn[i];
		xb[i]=xn[i];
		}
		
	ones=0;
	for(i=0;i<W2;++i)
		if(s[i]==1)
			r[ones++]=i;
	
	dflip=d;
	
	qsort(r,ones,sizeof(int),flipcompare);
	
	db=dwxn;
	for(j=0;j<num;++j)
		{
		db+=d[r[j]];
		
		wb[r[j]]=wf[r[j]];
		xb[r[j]]=xf[r[j]];
		}
	
	return db;
	}	

	
void ruleproj(int outnode,int *edge,double *w1o,double *x1o,double *w2o,double *x2o,double *yo,double *w1p,double *x1p,double *w2p,double *x2p,double *yp)
	{
	int sum1,sum2,c1,c2,i;
	int flipout,f1,f2;
	int s1[W2],s2[W2];
	double d1[W2],d2[W2],dwx1n,dwx2n;
	double w1n[W2],x1n[W2],w2n[W2],x2n[W2];
	double w1f[W2],x1f[W2],w2f[W2],x2f[W2];
	double w1a[W2],x1a[W2],w1b[W2],x1b[W2],w2a[W2],x2a[W2],w2b[W2],x2b[W2];
	
	double dist0,dist1,dist01,dist02;
	
	dwx1n=wxproj(omega1,edge,w1o,x1o,w1n,x1n,w1f,x1f,s1,d1);
	dwx2n=wxproj(omega2,edge,w2o,x2o,w2n,x2n,w2f,x2f,s2,d2);
		
	sum1=0;
	sum2=0;
	for(i=0;i<W2;++i)
		{
		sum1+=s1[i];
		sum2+=s2[i];
		}
		
	c1=sum1>=b1;
	c2=sum2<=b2;
	
	if(c1==0 && c2==0)
		{
		flipout=outnode && *yo>0.;
		
		dist0=sq(*yo+.5*eta)+dwx1n+dwx2n;
		
		dist1=sq(*yo-.5*eta);
		if(!outnode || flipout)
			{
			dist1+=aboveproj(b1-sum1,dwx1n,w1n,x1n,w1f,x1f,s1,d1,w1a,x1a);
			dist1+=belowproj(sum2-b2,dwx2n,w2n,x2n,w2f,x2f,s2,d2,w2b,x2b);
			}
		else
			dist1+=dwx1n+dwx2n;

		if(outnode)
			if(flipout)
				{
				f1=1;
				f2=-1;
				
				*yp=.5*eta;
				}
			else
				{
				f1=0;
				f2=0;
				
				*yp=-.5*eta;
				}
		else
			if(dist1<dist0)
				{
				f1=1;
				f2=-1;
				
				*yp=.5*eta;
				}
			else
				{
				f1=0;
				f2=0;
				
				*yp=-.5*eta;
				}
		}	
	else if(c1==1 && c2==1)
		{
		flipout=outnode && *yo<0.;
		
		dist1=sq(*yo-.5*eta)+dwx1n+dwx2n;
		
		dist0=sq(*yo+.5*eta);
		if(!outnode || flipout)
			{
			dist01=dwx2n+belowproj(sum1-b1+1,dwx1n,w1n,x1n,w1f,x1f,s1,d1,w1b,x1b);
			dist02=dwx1n+aboveproj(b2+1-sum2,dwx2n,w2n,x2n,w2f,x2f,s2,d2,w2a,x2a);
			
			dist0+=dist01<dist02 ? dist01 : dist02;
			}
		else
			dist0+=dwx1n+dwx2n;
		
		if(flipout || (!outnode && dist0<dist1))
			{
			if(dist01<dist02)
				{
				f1=-1;
				f2=0;
				}
			else
				{
				f1=0;
				f2=1;
				}
				
			*yp=-.5*eta;
			}
		else
			{
			f1=0;
			f2=0;
			
			*yp=.5*eta;
			}
		}	
	else if(c1==0 && c2==1)
		{
		flipout=outnode && *yo>0.;
		
		dist0=sq(*yo+.5*eta)+dwx1n+dwx2n;
		
		dist1=sq(*yo-.5*eta);
		if(!outnode || flipout)
			dist1+=dwx2n+aboveproj(b1-sum1,dwx1n,w1n,x1n,w1f,x1f,s1,d1,w1a,x1a);
		else
			dist1+=dwx1n+dwx2n;
		
		if(flipout || (!outnode && dist1<dist0))
			{
			f1=1;
			f2=0;
			
			*yp=.5*eta;
			}
		else
			{
			f1=0;
			f2=0;
			
			*yp=-.5*eta;
			}
		}
	else if(c1==1 && c2==0)
		{
		flipout=outnode && *yo>0.;
		
		dist0=sq(*yo+.5*eta)+dwx1n+dwx2n;
		
		dist1=sq(*yo-.5*eta);
		if(!outnode || flipout)
			dist1+=dwx1n+belowproj(sum2-b2,dwx2n,w2n,x2n,w2f,x2f,s2,d2,w2b,x2b);
		else
			dist1+=dwx1n+dwx2n;
		
		if(flipout || (!outnode && dist1<dist0))
			{
			f1=0;
			f2=-1;
			
			*yp=.5*eta;
			}
		else
			{
			f1=0;
			f2=0;
			
			*yp=-.5*eta;
			}
		}
		
	if(f1==0)
		{
		for(i=0;i<W2;++i)
			{
			w1p[edge[i]]=w1n[i];
			x1p[edge[i]]=x1n[i];
			}
		}
	else if(f1==1)
		{
		for(i=0;i<W2;++i)
			{
			w1p[edge[i]]=w1a[i];
			x1p[edge[i]]=x1a[i];
			}
		}
	else
		{
		for(i=0;i<W2;++i)
			{
			w1p[edge[i]]=w1b[i];
			x1p[edge[i]]=x1b[i];
			}
		}
		
	if(f2==0)
		{
		for(i=0;i<W2;++i)
			{
			w2p[edge[i]]=w2n[i];
			x2p[edge[i]]=x2n[i];
			}
		}
	else if(f2==1)
		{
		for(i=0;i<W2;++i)
			{
			w2p[edge[i]]=w2a[i];
			x2p[edge[i]]=x2a[i];
			}
		}
	else
		{
		for(i=0;i<W2;++i)
			{
			w2p[edge[i]]=w2b[i];
			x2p[edge[i]]=x2b[i];
			}
		}
	}


void projA(double *w1o,double *x1o,double *w2o,double *x2o,double **yo)
	{
	int p,l;
	
	for(p=0;p<space;++p)
	for(l=1;l<=steps;++l)
		ruleproj(l==steps,in[l][p],w1o,x1o,w2o,x2o,&yo[l][p],w1A,x1A,w2A,x2A,&yA[l][p]);
	}


void outconcur(int innode,int *edge,double *x1o,double *x2o,double *yo,double *x1p,double *x2p,double *yp)
	{
	double c;
	int i;
	
	if(innode)
		{
		*yp=*yo;
		
		for(i=0;i<W2;++i)
			{
			x1p[edge[i]]=(*yo)/eta;
			x2p[edge[i]]=(*yo)/eta;
			}
		}
	else
		{
		c=eta*(*yo);
	
		for(i=0;i<W2;++i)
			c+=x1o[edge[i]]+x2o[edge[i]];
			
		c/=eta+2.*W2/eta;
		
		*yp=c;
		
		c/=eta;
	
		for(i=0;i<W2;++i)
			{
			x1p[edge[i]]=c;
			x2p[edge[i]]=c;
			}
		}
	}
	

void projB(double *w1o,double *x1o,double *w2o,double *x2o,double **yo)
	{
	int p,l,i;
	double w1c,w2c;
	
	for(p=0;p<space;++p)
	for(l=0;l<steps;++l)
		outconcur(l==0,out[l][p],x1o,x2o,&yo[l][p],x1B,x2B,&yB[l][p]);
		
	for(i=0;i<W2;++i)
		{
		w1c=0.;
		w2c=0.;
		
		for(p=0;p<space;++p)
		for(l=1;l<=steps;++l)
			{
			w1c+=w1o[in[l][p][i]];
			w2c+=w2o[in[l][p][i]];
			}
			
		w1c/=space*steps;
		w2c/=space*steps;
		
		for(p=0;p<space;++p)
		for(l=1;l<=steps;++l)
			{
			w1B[in[l][p][i]]=w1c;
			w2B[in[l][p][i]]=w2c;
			}
		}
	}

	
void ref(double *w1o,double *x1o,double *w2o,double *x2o,double **yo)
	{
	int l,p,i,e;
	
	for(l=1;l<=steps;++l)
	for(p=0;p<space;++p)
		{
		for(i=0;i<W2;++i)
			{
			e=in[l][p][i];
			
			w1R[e]=2.*w1o[e]-w1[e];
			w2R[e]=2.*w2o[e]-w2[e];
			
			x1R[e]=2.*x1o[e]-x1[e];
			x2R[e]=2.*x2o[e]-x2[e];
			}
			
		yR[l][p]=2.*yo[l][p]-y[l][p];
		}
	}
	
	
void RRR(double *w1err,double *w2err,double *xerr,double *yerr)
	{
	int l,p,i,e;
	double diff;
	
	if(beta>0.)
		{
		projA(w1,x1,w2,x2,y);
		ref(w1A,x1A,w2A,x2A,yA);
		projB(w1R,x1R,w2R,x2R,yR);
		}
	else
		{
		projB(w1,x1,w2,x2,y);
		ref(w1B,x1B,w2B,x2B,yB);
		projA(w1R,x1R,w2R,x2R,yR);
		}
		
	*w1err=0.;
	*w2err=0.;
	*xerr=0.;
	*yerr=0.;
	
	for(l=1;l<=steps;++l)
	for(p=0;p<space;++p)
		{
		for(i=0;i<W2;++i)
			{
			e=in[l][p][i];
			
			diff=w1B[e]-w1A[e];
			w1[e]+=beta*diff;
			*w1err+=diff*diff;
			
			diff=w2B[e]-w2A[e];
			w2[e]+=beta*diff;
			*w2err+=diff*diff;
			
			diff=x1B[e]-x1A[e];
			x1[e]+=beta*diff;
			*xerr+=diff*diff;
			
			diff=x2B[e]-x2A[e];
			x2[e]+=beta*diff;
			*xerr+=diff*diff;
			}
			
		if(l<steps)
			{
			diff=yB[l][p]-yA[l][p];
			y[l][p]+=beta*diff;
			*yerr+=diff*diff;
			}
		}
		
	*w1err=sqrt(*w1err/(2.*W2*space*steps))/omega1;
	*w2err=sqrt(*w2err/(2.*W2*space*steps))/omega2;
	*xerr=sqrt(*xerr/(2.*W2*space*steps));
	*yerr=sqrt(*yerr/(space*(steps-1)))/eta;
	}
	
  
void setup()
	{
	int edges,l,p1,p2,p,r1,r2,r,q1,q2,q;
	
	space=size*size;
	
	w1=malloc(steps*space*W2*sizeof(double));
	w1A=malloc(steps*space*W2*sizeof(double));
	w1B=malloc(steps*space*W2*sizeof(double));
	w1R=malloc(steps*space*W2*sizeof(double));
	
	w2=malloc(steps*space*W2*sizeof(double));
	w2A=malloc(steps*space*W2*sizeof(double));
	w2B=malloc(steps*space*W2*sizeof(double));
	w2R=malloc(steps*space*W2*sizeof(double));
	
	x1=malloc(steps*space*W2*sizeof(double));
	x1A=malloc(steps*space*W2*sizeof(double));
	x1B=malloc(steps*space*W2*sizeof(double));
	x1R=malloc(steps*space*W2*sizeof(double));
	
	x2=malloc(steps*space*W2*sizeof(double));
	x2A=malloc(steps*space*W2*sizeof(double));
	x2B=malloc(steps*space*W2*sizeof(double));
	x2R=malloc(steps*space*W2*sizeof(double));
	
	in=malloc((steps+1)*sizeof(int**));
	out=malloc((steps+1)*sizeof(int**));
	
	for(l=0;l<=steps;++l)
		{
		in[l]=malloc(space*sizeof(int*));
		out[l]=malloc(space*sizeof(int*));
		
		for(p=0;p<space;++p)
			{
			in[l][p]=malloc(W2*sizeof(int));
			out[l][p]=malloc(W2*sizeof(int));
			}
		}
	
	edges=0;
	for(l=1;l<=steps;++l)
	for(p1=0;p1<size;++p1)
	for(p2=0;p2<size;++p2)
		{
		p=size*p1+p2;
		
		for(r1=0;r1<W;++r1)
		for(r2=0;r2<W;++r2)
			{
			r=W*r1+r2;
			
			q1=sgnmod(p1+r1-D);
			q2=sgnmod(p2+r2-D);
			
			q=size*q1+q2;
		
			in[l][p][r]=edges;
			out[l-1][q][r]=edges;
			
			++edges;
			}
		}
	
	y=malloc((steps+1)*sizeof(double*));
	yA=malloc((steps+1)*sizeof(double*));
	yB=malloc((steps+1)*sizeof(double*));
	yR=malloc((steps+1)*sizeof(double*));
	
	for(l=0;l<=steps;++l)
		{
		y[l]=malloc(space*sizeof(double));
		yA[l]=malloc(space*sizeof(double));
		yB[l]=malloc(space*sizeof(double));
		yR[l]=malloc(space*sizeof(double));
		}
	}
	
	
int getdata(char *datafile)
	{
	FILE *fp;
	int l,p1,p2,p,state;
	char data[SMAX];
	
	fp=fopen(datafile,"r");
	if(!fp)
		{
		printf("cannot open datafile\n");
		return 0;
		}
	
	l=0;	
	p1=0;
	while(fgets(data,SMAX,fp)!=NULL)
		{
		if(l==0 && p1==0)
			{
			size=strlen(data)-1;
			
			setup();
			}
		else if(strlen(data)==1)
			{
			l=steps;
			p1=0;
				
			continue;
			}
			
		for(p2=0;p2<size;++p2)
			{
			p=size*p1+p2;
			
			state=data[p2]-'0';
			
			y[l][p]=eta*((double)state-.5);
			yA[l][p]=y[l][p];
			yB[l][p]=y[l][p];
			yR[l][p]=y[l][p];
			}
			
		++p1;
		}
	
	fclose(fp);
	
	return 1;
	}
	

double sgnrand()
  {
  return ((double)rand())/RAND_MAX-.5;
  }
  
  
void randstart()
	{
	int l,p,i,e;
	
	for(l=1;l<=steps;++l)
	for(p=0;p<space;++p)
		{
		for(i=0;i<W2;++i)
			{
			e=in[l][p][i];
			
			x1[e]=sgnrand();
			x2[e]=sgnrand();
			
			w1[e]=omega1*sgnrand();
			w2[e]=omega2*sgnrand();
			}
			
		if(l<steps)
			y[l][p]=eta*sgnrand();
		}
	}
	
	
void printparam(FILE *fp)
	{
	int i;
	
	for(i=0;i<W2;++i)
		fprintf(fp,"%6.2lf",w1B[in[1][0][i]]/omega1+.5);
		
	fprintf(fp,"   ");
	
	for(i=0;i<W2;++i)
		fprintf(fp,"%6.2lf",w2B[in[1][0][i]]/omega2+.5);
		
	fprintf(fp,"\n");
	}
	
	
int solve(int itermax,int iterstride,double stoperr)
	{
	int iter;
	double w1err,w2err,xerr,yerr;
	FILE *fp1,*fp2;
	
	fp1=fopen(errfile,"w");
	fp2=fopen(paramfile,"w");
	
	for(iter=1;iter<=itermax;++iter)
		{
		RRR(&w1err,&w2err,&xerr,&yerr);
		
		if(iter%iterstride==0)
			{
			fprintf(fp1,"%10.6lf%10.6lf%10.6lf%10.6lf\n",w1err,w2err,xerr,yerr);
			
			printparam(fp2);
			}
		
		if(w1err+w2err+xerr+yerr<stoperr)
			{
			fprintf(fp1,"%10.6lf%10.6lf%10.6lf%10.6lf\n",w1err,w2err,xerr,yerr);
			
			printparam(fp2);
			
			fclose(fp1);
			fclose(fp2);
			
			return iter;
			}
		}
			
	fclose(fp1);
	fclose(fp2);
			
	return 0;
	}


void printsol(char *solfile)
	{
	FILE *fp;
	int i;
	
	fp=fopen(solfile,"a");
	
	for(i=0;i<W2;++i)
		fprintf(fp,"%1d",w1B[in[1][0][i]]<0. ? 0 : 1);
	
	fprintf(fp," ");
	
	for(i=0;i<W2;++i)
		fprintf(fp,"%1d",w2B[in[1][0][i]]<0. ? 0 : 1);
		
	fprintf(fp,"\n");
	
	fclose(fp);
	}


int main(int argc,char* argv[])
	{
	char *datafile,*id;
	int iter,itermax,iterstride,trials,t,c,solcount;
	double stoperr,iterave,elapsed,iterpersec;
	FILE *fp;
	clock_t start;
	
	
	if(argc==14)
		{
		datafile=argv[1];
		steps=atoi(argv[2]);
		b1=atoi(argv[3]);
		b2=atoi(argv[4]);
		omega1=atof(argv[5]);
		omega2=atof(argv[6]);
		eta=atof(argv[7]);
		beta=atof(argv[8]);
		itermax=atoi(argv[9]);
		iterstride=atoi(argv[10]);
		stoperr=atof(argv[11]);
		trials=atoi(argv[12]);
		id=argv[13];
		}
	else
		{
		printf("expected thirteen arguments: datafile, steps, b1, b2, omega1, omega2, eta, beta, itermax, iterstride, stoperr, trials, id\n");
		return 1;
		}
	
	if(!getdata(datafile))
		return 1;
	
	sprintf(errfile,"%s.err",id);
	sprintf(paramfile,"%s.param",id);
	sprintf(statsfile,"%s.stats",id);
	sprintf(solfile,"%s.sol",id);
	
	fp=fopen(statsfile,"w");
	
	for(c=0;c<argc;++c)
    	fprintf(fp,"%s ",argv[c]);
    fprintf(fp,"\n\n");
	
	fclose(fp);
	
	fp=fopen(solfile,"w");
	fclose(fp);
	
	srand(time(NULL));
	start=clock();
	
	solcount=0;
	iterave=0.;
	for(t=1;t<=trials;++t)
		{
		randstart();
		
		iter=solve(itermax,iterstride,stoperr);
		
		if(iter)
			{
			++solcount;
			iterave+=iter;
			
			printsol(solfile);
			}
		else
			iterave+=itermax;
		
		fp=fopen(statsfile,"a");
		fprintf(fp,"%3d%12d\n",t,iter);
		fclose(fp);
		}
	
	elapsed=((double)(clock()-start))/CLOCKS_PER_SEC;
	
	iterpersec=iterave/elapsed;
	
	iterave/=solcount;
	
	fp=fopen(statsfile,"a");
	fprintf(fp,"\n %d/%d solutions%10.2e iterations/solution%10.2lf iterations/sec%10.2lf sec/solution\n",solcount,trials,iterave,iterpersec,iterave/iterpersec);
	fclose(fp);
	
	return 0;
	}
