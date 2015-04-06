/**
Copyright (C) 2015  Cristian Alfonso Prieto Sánchez

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

package ugr.cristian.serverVideoApp;

import java.util.Dictionary;
import java.util.Hashtable;

import org.apache.felix.dm.Component;
import org.opendaylight.controller.sal.core.ComponentActivatorAbstractBase;
import org.opendaylight.controller.sal.flowprogrammer.IFlowProgrammerService;
import org.opendaylight.controller.sal.packet.IDataPacketService;
import org.opendaylight.controller.sal.packet.IListenDataPacket;
import org.opendaylight.controller.sal.routing.IRouting;
import org.opendaylight.controller.switchmanager.ISwitchManager;
import org.opendaylight.controller.topologymanager.ITopologyManager;
import org.opendaylight.controller.statisticsmanager.IStatisticsManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Activator extends ComponentActivatorAbstractBase {
    private static final Logger log = LoggerFactory.getLogger(PacketHandler.class);


    /**
     * Function called when the activator starts just after some
     * initializations are done by the
     * ComponentActivatorAbstractBase.
     *
     */
    public void init() {
    }

    /**
     * Function called when the activator stops just before the
     * cleanup done by ComponentActivatorAbstractBase
     *
     */
    public void destroy() {

    }


    /**
     * Function that is used to communicate to dependency manager the
     * list of known implementations for services inside a container
     *
     * @return An array containing all the CLASS objects that will be
     * instantiated in order to get an fully working implementation
     * Object
     */
    public Object[] getImplementations() {
        log.trace("Getting Implementations");

        Object[] res = { PacketHandler.class };
        return res;
    }

    /**
     * Function that is called when configuration of the dependencies
     * is required.
     *
     * @param c dependency manager Component object, used for
     * configuring the dependencies exported and imported
     * @param imp Implementation class that is being configured,
     * needed as long as the same routine can configure multiple
     * implementations
     * @param containerName The containerName being configured, this allow
     * also optional per-container different behavior if needed, usually
     * should not be the case though.
     */

    public void configureInstance(Component c, Object imp, String containerName) {
        log.trace("Configuring instance");

        if (imp.equals(PacketHandler.class)) {
            // Define exported and used services for PacketHandler component.

            Dictionary<String, Object> props = new Hashtable<String, Object>();
            props.put("salListenerName", "myPacketHandler");

            // Export IListenDataPacket interface to receive packet-in events.
            c.setInterface(new String[] {IListenDataPacket.class.getName()}, props);

            // Need the DataPacketService for encoding, decoding, sending data packets
            c.add(createContainerServiceDependency(containerName).setService(
                    IDataPacketService.class).setCallbacks(
                    "setDataPacketService", "unsetDataPacketService")
                    .setRequired(true));

            // Need SwitchManager service for enumerating ports of switch
            c.add(createContainerServiceDependency(containerName).setService(
                    ISwitchManager.class).setCallbacks(
                    "setSwitchManagerService", "unsetSwitchManagerService")
                    .setRequired(true));

            // Need FlowProgrammerService for programming flows
            c.add(createContainerServiceDependency(containerName).setService(
                    IFlowProgrammerService.class).setCallbacks(
                    "setFlowProgrammerService", "unsetFlowProgrammerService")
                    .setRequired(true));

            //Need a StatisticsManagerService to try to resolve new challenges.
            c.add(createContainerServiceDependency(containerName).setService(
                    IStatisticsManager.class).setCallbacks(
                    "setStatisticsManagerService", "unsetStatisticsManagerService")
                    .setRequired(true));

            //Need a TopologyManagerService to try to obtain map with the topology
            c.add(createContainerServiceDependency(containerName).setService(
                    ITopologyManager.class).setCallbacks(
                    "setTopologyManagerService", "unsetTopologyManagerService")
                    .setRequired(true));
        }

    }
}
