
control Port(inout headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {


action set_port_status(bit<8> livePorts) {
    meta.ports.status = livePorts;
    meta.ports.mdValid = 1;
}

table port_status {
    actions = {
        set_port_status;
    }
}

apply {
    if(meta.ports.mdValid == 0) {
        port_status.apply();
    }
}

}
