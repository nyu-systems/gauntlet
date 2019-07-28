control egress(inout headers hdr,
			   inout metadata meta,
			   inout standard_metadata_t standard_metadata) {

	Bier() bier_c;
	Mac() mac_c;

	apply {

	    if ((hdr.ethernet.etherType == TYPE_BIER) && standard_metadata.instance_type == PKT_INSTANCE_TYPE_INGRESS_CLONE) { // its a cloned bier packet
			bier_c.apply(hdr, meta, standard_metadata); // apply bier control for cloned packets
		}

		mac_c.apply(hdr, meta, standard_metadata); // set layer 2 addresses if rules are set
	}
}
