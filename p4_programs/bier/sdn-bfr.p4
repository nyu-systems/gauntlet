/* -*- P4_16 -*- */

#include <core.p4>
#include <v1model.p4>

// headers
#include "src/components/headers.p4"

// parser
#include "src/components/parser.p4"

// port status
#include "src/components/controls/Port.p4"

// bier control
#include "src/components/controls/Bier.p4"

// ip control
#include "src/components/controls/Ipv4.p4"

// mac control
#include "src/components/controls/Mac.p4"

// topology discovery control
#include "src/components/controls/Topology-Discovery.p4"

// ingress control
#include "src/components/ingress.p4"

// egress control
#include "src/components/egress.p4"

// checksum control
#include "src/components/checksum.p4"

// deparser
#include "src/components/deparser.p4"

/*************************************************************************
***********************  S W I T C H  *******************************
*************************************************************************/

V1Switch(
	packetParser(),
	verifyChecksum(),
	ingress(),
	egress(),
	createChecksum(),
	deparser()
	) main;
