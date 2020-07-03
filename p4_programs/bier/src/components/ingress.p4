/* Control unit for ingress
* First checks if its a normal ipv4 packet and applies ipv4 control unit
* Otherwise checks if its a BIER packet and applies bier control
*/
control ingress(inout headers hdr,
				inout metadata meta,
				inout standard_metadata_t standard_metadata) {

	Port() port_c;
    Bier() bier_c; // bier control unit
    IPv4() ipv4_c; // ipv4 control unit
    TopologyDiscovery() topology_c; // topology control unit

    apply {

		port_c.apply(hdr, meta, standard_metadata); // apply port status table, init port meta data

        if (hdr.ethernet.etherType == TYPE_BIER) { // its a bier packet
            bier_c.apply(hdr, meta, standard_metadata); // apply bier control
        }
        else if(hdr.ethernet.etherType == TYPE_IPV4) { // its a ipv4 packet, and not destinated for a subdomain
            ipv4_c.apply(hdr, meta, standard_metadata);  // apply ipv4 control
        }
        else if(hdr.ethernet.etherType == TYPE_TOP_DISCOVER) { // its a topology discovery packet
            topology_c.apply(hdr, meta, standard_metadata);
        }
    }
}
