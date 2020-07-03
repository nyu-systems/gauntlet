control TopologyDiscovery(inout headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

	apply {
		if(standard_metadata.ingress_port == CONTROLLER_PORT) { // its a topology packet from the controller
			standard_metadata.mcast_grp = 1; // do flooding based on configured mc group
		}
		else {
			standard_metadata.egress_spec = CONTROLLER_PORT; // send to controller
			hdr.topology.port = (bit<16>) standard_metadata.ingress_port;

		}

	}
}
