/* Header plans: proved-image identity, reference parity and policy publication. */
#include "cet_profile.h"
#include "p1_load.h"
#include "tisa_ref.h"
#include "tisa_x86.h"
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    const uint64_t *plan, *plan_end;
    uint64_t *ctl;
    const uint64_t *bind, *leaves;
    uint64_t budget, used;
    const uint64_t *at;
} TcDrive;
_Static_assert(sizeof(TcDrive) == 64 && offsetof(TcDrive, ctl) == 16 &&
               offsetof(TcDrive, bind) == 24 && offsetof(TcDrive, leaves) == 32 &&
               offsetof(TcDrive, budget) == 40 && offsetof(TcDrive, used) == 48 &&
               offsetof(TcDrive, at) == 56, "driver layout");
uint64_t tisa_drive(TcDrive *descriptor);
extern const uint8_t hdr_eqw[], hdr_eqw_end[], hdr_pol[], hdr_pol_end[];
extern const uint8_t hdr_leb[], hdr_leb_end[], hdr_const[], hdr_const_end[];
extern const uint8_t hdr_cur[], hdr_cur_end[], hdr_inc[], hdr_inc_end[];

enum { NCTL = 32, NBIND = 64, STEPW = 18, MAXSTEP = 32, INPUT = 128, MAGIC = 39, GUARD = 8 };
typedef struct {
    uint64_t before[GUARD], cw[NCTL], after[GUARD];
    uint64_t sbefore[GUARD], state[2], safter[GUARD];
    uint8_t ibefore[64], input[INPUT], iafter[64];
    uint8_t mbefore[64], magic[MAGIC], mafter[64];
    uint64_t bind[NBIND], leaves[33];
} Side;
typedef struct { uint64_t status, at, used; } Result;
static P1Program programs[6];
static const unsigned codes[6] = {3,20,26,31,25,32};
static const char *names[6] = {"eqw","pol_max","leb_next","const_next","cur","inc"};
static const uint8_t *images[6], *ends[6];
static uint64_t rng = UINT64_C(0x9E3779B97F4A7C15), cases, checks, failures, failed_changes;

static uint64_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return rng;
}
static void require(int ok, const char *why) {
    checks++;
    if (!ok) {
        failures++;
        if (failures < 12) fprintf(stderr,"case %" PRIu64 ": %s\n",cases,why);
    }
}
static int exact_image(const char *path, const uint8_t *image, size_t length) {
    FILE *file = fopen(path,"rb");
    if (!file) return 0;
    int byte, ok = 1;
    size_t i = 0;
    while ((byte = fgetc(file)) != EOF) {
        if (i >= length || image[i] != (uint8_t)byte) ok = 0;
        i++;
    }
    ok = ok && !ferror(file) && i == length;
    fclose(file);
    return ok;
}
static void bind_side(Side *s, size_t length) {
    memset(s->bind,0,sizeof s->bind);
    s->bind[54] = (uint64_t)(uintptr_t)s->input; s->bind[55] = length;
    s->bind[58] = (uint64_t)(uintptr_t)s->state; s->bind[59] = sizeof s->state;
    s->bind[60] = (uint64_t)(uintptr_t)s->magic; s->bind[61] = MAGIC;
    for (size_t j=0;j<33;j++) s->leaves[j]=(uint64_t)(uintptr_t)hdr_eqw;
    for (size_t j=0;j<6;j++) s->leaves[codes[j]]=(uint64_t)(uintptr_t)images[j];
}
static const TcIsaProgram *program(unsigned code) {
    for (size_t j=0;j<6;j++) if (codes[j]==code) return &programs[j].prog;
    fprintf(stderr,"unknown test leaf %u\n",code); exit(2);
}
static Result reference(Side *s, const uint64_t *plan, size_t steps, uint64_t budget, uint64_t used) {
    for (size_t i=0;i<steps;i++) {
        const uint64_t *st=plan+i*STEPW;
        if (used>budget) return (Result){3,i,used};
        TcIsaRuntimeFrame frame;
        uint64_t *words=(uint64_t *)&frame;
        memset(&frame,0,sizeof frame);
        for (size_t r=0;r<9;r++) {
            words[2*r]=s->bind[st[1+r]]; words[2*r+1]=s->bind[st[1+r]+1];
        }
        frame.fuel_budget=budget; frame.fuel_used=used;
        frame.arg0=s->cw[st[10]]; frame.arg1=s->cw[st[11]];
        uint64_t regs[TISA_NUM_VREGS]={0}; regs[0]=(uint64_t)(uintptr_t)&frame;
        for (size_t r=1;r<=5;r++) regs[r]=s->cw[st[11+r]];
        (void)tisa_run(program((unsigned)st[0]),&frame,regs);
        s->cw[st[17]]=frame.ret_val; used=frame.fuel_used;
        if (frame.status!=1) return (Result){frame.status,i,used};
    }
    return (Result){1,steps,used};
}
static size_t leb(uint8_t *out, uint64_t value) {
    size_t n=0;
    do { uint8_t byte=value&127; value>>=7; out[n++]=byte|(value?128:0); } while (value);
    return n;
}
static void trial(const uint64_t *plan, size_t count, const uint8_t magic[MAGIC],
                  uint64_t floor, uint64_t proposed, unsigned variant, size_t prefix,
                  uint64_t budget, uint64_t used, int mutation) {
    Side original, ref, native;
    memset(&original,0xA5,sizeof original);
    for (size_t j=0;j<NCTL;j++) original.cw[j]=next();
    for (size_t j=0;j<=6;j++) original.cw[j]=j;
    original.cw[7]=floor; original.cw[17]=0; original.cw[19]=0;
    original.cw[20]=variant==6; original.state[0]=0; original.state[1]=next();
    memcpy(original.magic,magic,MAGIC); memcpy(original.input,magic,MAGIC);
    size_t length=MAGIC;
    if (variant==1) original.input[0]^=1;
    if (variant==8) { original.input[length++]=0x81; original.input[length++]=0; }
    else length+=leb(original.input+length,variant==2?2:1);
    length+=leb(original.input+length,variant==3?1:0);
    if (variant==5) { original.input[length++]=0x80; original.input[length++]=0; }
    else length+=leb(original.input+length,proposed);
    length+=leb(original.input+length,variant==4?1:0);
    if (variant==7) length--;
    memcpy(&ref,&original,sizeof ref); memcpy(&native,&original,sizeof native);
    bind_side(&ref,length); bind_side(&native,length);
    uint64_t altered[MAXSTEP*STEPW]; memcpy(altered,plan,count*STEPW*sizeof(uint64_t));
    for (size_t i=0;i<count;i++) {
        uint64_t *st=altered+i*STEPW;
        if (mutation==1 && st[0]==20) st[17]=7;
        if ((mutation==1 || mutation==2) && st[0]==3 && st[10]==25 && st[11]==25 && st[17]==7) {
            st[10]=0; st[11]=0; st[17]=27;
        }
        if (mutation==3 && st[0]==20) { st[0]=3; st[10]=26; st[11]=26; }
    }
    Result wanted=reference(&ref,plan,prefix,budget,used);
    TcDrive d={altered,altered+prefix*STEPW,native.cw,native.bind,native.leaves,budget,used,NULL};
    uint64_t status=tisa_drive(&d);
    cases++;
    require(status==wanted.status,"outcome parity");
    require(d.at==altered+wanted.at*STEPW,"stopping step parity");
    require(d.used==wanted.used && d.budget==budget,"receipt parity");
    for (size_t j=0;j<NCTL;j++) require(native.cw[j]==ref.cw[j],"control word parity");
    require(!memcmp(native.state,ref.state,sizeof native.state),"reader state parity");
    require(!memcmp(native.input,original.input,INPUT),"input read-only");
    require(!memcmp(native.magic,magic,MAGIC),"constant read-only");
    require(!memcmp(native.before,original.before,sizeof native.before) &&
            !memcmp(native.after,original.after,sizeof native.after),"control guards");
    require(!memcmp(native.sbefore,original.sbefore,sizeof native.sbefore) &&
            !memcmp(native.safter,original.safter,sizeof native.safter),"state guards");
    require(!memcmp(native.ibefore,original.ibefore,64) && !memcmp(native.iafter,original.iafter,64) &&
            !memcmp(native.mbefore,original.mbefore,64) && !memcmp(native.mafter,original.mafter,64),"byte guards");
    if (prefix==count) {
        if (wanted.status==1) {
            require(variant==0 && proposed<=2,"successful header has valid guards");
            require(native.cw[7]==(floor>proposed?floor:proposed) && native.cw[20]==1,"policy/header publication");
            require(native.state[0]==length,"successful cursor");
        } else {
            if (native.cw[7]!=floor) failed_changes++;
            require(native.cw[7]==floor,"refused header keeps host policy");
            require(native.cw[20]==original.cw[20],"refused header keeps HDR");
        }
    }
}

int main(int argc,char **argv) {
    if (argc<5 || argc>6) { fprintf(stderr,"usage: test_header WORK PLAN.words HEADER.bytes LEAFDIR [MUTATION]\n"); return 2; }
    int mutation=0;
    if (argc==6) {
        if (!strcmp(argv[5],"--early-policy")) mutation=1;
        else if (!strcmp(argv[5],"--skip-publication")) mutation=2;
        else if (!strcmp(argv[5],"--bypass-policy-guard")) mutation=3;
        else return 2;
    }
    if (!cet_profile()) return 2;
    images[0]=hdr_eqw; images[1]=hdr_pol; images[2]=hdr_leb; images[3]=hdr_const;
    images[4]=hdr_cur; images[5]=hdr_inc;
    ends[0]=hdr_eqw_end; ends[1]=hdr_pol_end; ends[2]=hdr_leb_end; ends[3]=hdr_const_end;
    ends[4]=hdr_cur_end; ends[5]=hdr_inc_end;
    char path[4096]; snprintf(path,sizeof path,"%s/driver.bin",argv[1]);
    if (!exact_image(path,(const uint8_t *)(uintptr_t)tisa_drive,522)) return 2;
    for (size_t i=0;i<6;i++) {
        snprintf(path,sizeof path,"%s/%s.bin",argv[1],names[i]);
        size_t length=(size_t)((uintptr_t)ends[i]-(uintptr_t)images[i]);
        if (!exact_image(path,images[i],length)) return 2;
        snprintf(path,sizeof path,"%s/%s/%s_prog.txt",argv[4],names[i],names[i]);
        TcIsaTextStyle style; P1Error error;
        if (!p1_load_file(path,&programs[i],&style,&error)) { p1_print_error(stderr,path,&error); return 2; }
        TcIsaX86 image; char reason[256];
        if (!tisa_x86_emit(&programs[i].prog,&image,reason,sizeof reason)) { fprintf(stderr,"emit: %s\n",reason); return 2; }
        int same=image.len==length && !memcmp(image.bytes,images[i],length);
        tisa_x86_free(&image);
        if (!same) { fprintf(stderr,"program/image mismatch: %s\n",names[i]); return 2; }
    }
    uint64_t plan[MAXSTEP*STEPW],value;
    FILE *file=fopen(argv[2],"r"); if (!file) return 2;
    size_t words=0;
    while (fscanf(file,"%" SCNu64,&value)==1) { if (words>=MAXSTEP*STEPW) return 2; plan[words++]=value; }
    int valid=feof(file) && !ferror(file) && words && words%STEPW==0; fclose(file); if (!valid) return 2;
    size_t steps=words/STEPW;
    uint8_t magic[MAGIC]; file=fopen(argv[3],"r"); if (!file) return 2;
    for (size_t i=0;i<MAGIC;i++) { if (fscanf(file,"%" SCNu64,&value)!=1 || value>255) return 2; magic[i]=(uint8_t)value; }
    if (fscanf(file,"%" SCNu64,&value)!=EOF || ferror(file)) return 2;
    fclose(file);
    const uint64_t budgets[]={0,1,38,39,42,43,44,UINT64_MAX};
    const uint64_t proposals[]={0,1,2,3,UINT64_MAX};
    for (uint64_t floor=0;floor<=2;floor++)
        for (size_t p=0;p<sizeof proposals/sizeof proposals[0];p++)
            for (unsigned variant=0;variant<9;variant++)
                for (size_t prefix=0;prefix<=steps;prefix++)
                    for (size_t b=0;b<sizeof budgets/sizeof budgets[0];b++)
                        trial(plan,steps,magic,floor,proposals[p],variant,prefix,budgets[b],0,mutation);
    printf("header plans: %" PRIu64 " cases, %" PRIu64 " checks, %" PRIu64 " failures; failed-policy-changes %" PRIu64 "\n",
           cases,checks,failures,failed_changes);
    return failures?1:0;
}
