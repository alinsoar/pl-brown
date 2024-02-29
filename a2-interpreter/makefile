
all:
	@2>&1 ./debian-dist/bin/assignment2-debian  --report | \
	sed \
	-e 's:["][(]:\n:g;' \
	-e 's:[)][\]["]:\n---\n:g ;' \
	-e 's:, \\::g;' \
	-e 's:[]]["]::;' \
	-e 's:[\][\]::g ;' \
	-e 's:[\]["]::g;' \
	-e 's:,:\n:g' \
	-e 's:interp:@I:g' \
	-e 's:parse:@P:g' \
	-e 's:quote:@Q:g'

rep:
	@./debian-dist/bin/assignment2-debian  --report

# -e 's:(parse (quote:PQ:g' | \
# sed \
# -e '/ PQ/ s:[)][)] 10 : --- :g;' \
# -e '/ IPQ/ s:[)][)][)] 10 : --- :g;'


