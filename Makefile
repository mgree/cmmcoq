METALIB = ../../provers/metalib/trunk
OTT = ott

all:
	+make -C $(METALIB) Metatheory.vo
	+make -C $(METALIB) AssumeList.vo
	+make -C $(METALIB) LibDefaultSimp.vo
	+make main

############################################################################ 
COQC = coqc -I .
COQDEP = coqdep

FILES = \
        terms \
	infrastructure \
	prelim \
	thy

pat: $(foreach i, $(PAT), $(i).vo)
core: $(foreach i, $(CORE), $(i).vo)

############################################################################

VFILES = $(foreach i, $(FILES), $(i).v)
VOFILES = $(foreach i, $(FILES), $(i).vo)

.PHONY: all clean default
.SUFFIXES: .v .vo


main : $(VOFILES) 

clean :
	rm -f *.vo .depend *.glob

.v.vo : .depend
	$(COQC) -I $(METALIB) $<

.depend : $(VFILES)
	$(COQDEP) -I . -I  $(METALIB) $(VFILES) > .depend

include .depend

terms.v : terms.ott
	ott  -coq_expand_list_types true -coq terms.v \
           terms.ott

infrastructure.v : terms.v
	lngen  --coq=infrastructure.v --coq-ott=terms \
           --coq-loadpath=$(METALIB) terms.ott
