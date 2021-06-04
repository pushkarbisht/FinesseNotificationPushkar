
/**
 * @fileOverview The Event Tunnel resides on the Finesse system to establish
 *     an event Websocket connection with the notification server. The idea is for
 *     the master frame to create a hidden IFRAME pointing to the Event
 *     Tunnel HTML page, importing this JS. Since there is a cross-domain
 *     restriction between frames, window.postMessage is used to communicate.
 *     This allows the Websocket connection with the strophe library to be
 *     established within third-party containers.
 * @author <a href="mailto:habui@cisco.com">Harry Bui</a>
 * @name EventTunnel
 * @requires strophe, finesse.Utilities
 */

/** @namespace */
var finesse = finesse || {};

/**
 * @class
 * Create a Websocket connection (using strophe) with the notification server to
 * receive events. Events are delivered through the communication tunnel with
 * the parent frame. After the creation of the EventTunnel object, the init
 * must be called to start listening for messages from the parent frame. Websocket
 * connection establishment starts when the parent frame sends the credentials
 * (via message tunnel).
 * @constructor
 * @throws {Error} If required constructor parameter is missing.
 */
finesse.EventTunnel = function () {

    var

    /**
     * Required for scope issues
     * @private
     */
	_this = this,

    /**
     * Flag to determine whether running in Internet Explorer. Used for disconnect logic
     */
    _isIE,

    /**
     * Short reference to the Finesse utility.
     * @private
     */
    _util = finesse.EventTunnel.Utilities,

    /**
     * The JabbwerWerx client object after connection has been made.
     * @private
     */
    _jwClient,
    
    /**
     * The XMPP client object after connection has been made. (via Strophe.js)
     * @private
     */
    _xmppClient,
    
    
    /**
     * The XMPP client connection status after connection has been made.
     * @private
     */
    _xmppClientStatus, 
    
     
    /**
     * The XMPP client connection RESOURCE.
     * @private
     */
    _xmppResource, 
    /**
     * The ID of the user logged into notification server.
     * @private
     */
    _id,

    /**
     * The resource to use for the Websocket connection.
     * @private
     */
    _resource,

    /**
     * The domain of the XMPP server, representing the portion of the JID
     * following '@': userid@domain.com
     * @private
     */
    _xmppDomain,

    /**
     * The password of the user logged into notification server.
     * @private
     */
    _password,

    /**
     * The jid of the pubsub service on the XMPP server
     * @private
     */
    _pubsubDomain,
    
    /**
     * The xmpp protocol type : websocket or BOSH
     * We are setting the default value as bosh so that custom clients upgrading to 12.0 
     * will not break(backward compatibility), the custom clients will continue to work on bosh and finesse desktop
     * will use the desktop properties to pass the notificationType. By default finesse desktop
     * will connect using websocket.
     * @private
     */
    _notificationConnectionType="bosh",

    /**
     * Internal store of strophe.PubSubNode objects, used for unload cleanup
     * @private
     */
	_pubsubNodes = [],

    /**
     * The different types of messages that could be sent to the parent frame.
     * The types here should be understood by the parent frame and used to
     * identify how the message is formatted.
     * @private
     */
    _TYPES = {
        EVENT: 0,
        ID: 1,
        PASSWORD: 2,
        RESOURCEID: 3,
        STATUS: 4,
		XMPPDOMAIN: 5,
		PUBSUBDOMAIN: 6,
		SUBSCRIBE: 7,
		UNSUBSCRIBE: 8,
		PRESENCE: 9,
		CONNECT_REQ: 10,
		DISCONNECT_REQ: 11,
		NOTIFICATION_CONNECTION_TYPE: 12,
        LOGGING: 13,
        SUBSCRIPTIONS_REQ: 14,
        XMPP_DISCONNECT_PROPERTIES: 15
    },

    /**
     * Describes the states of the strophe Websocket connection. Other than the
     * "loaded", these states map directly with strophe's status mapping.
     * @private
     */
    _STATUS = [
        "loaded",
        "connecting",
        "connected",
        "disconnected",
        "disconnecting",
        "reconnecting",
        "unloading"
    ],
    
    NUMBER_OF_PING_RETRY = 2,

    /**
     * Flag to indicate whether Openfire is connected or not
     * @type {Boolean}
     * @private
     */
    _isConnected = false,
    
    /**
     * Flag to indicate whether initial presence has been received by the XMPP
     * server.
     * 
     * @private
     */
    _initPresence = false,
    
    _pingCounter = 0,
    
    _pingIntervalHandler = null,

    _xmppProperties = {
        xmppFailoverRequestMaxRetry: NUMBER_OF_PING_RETRY,
        xmppRequestTimeout: 10000,
        xmppFailoverDetectionPingInterval: 10000
    },

    /**
     * Communicates with the parent frame (should be the Master gadget) by
     * sending a message formatted as follows "type|message".
     * @param {Number} type
     *     The category type of the message.
     * @param {String} message
     *     The message to be sent to the parent frame.
     * @private
     */
    _sendMessage = function (type, message) {
        message = type + "|" + message;
        _util.sendMessage(message, parent);
    },
    
    _log = function (msg) {
        _sendMessage(_TYPES.LOGGING, msg);
	},
    
    _isInternetExplorer = function () {
            var ua = window.navigator.userAgent;

            var msie = ua.indexOf('MSIE ');
            if (msie > 0) {
                // IE 10 or older => return version number
                return true;
            }

            var trident = ua.indexOf('Trident/');
            if (trident > 0) {
                // IE 11 => return version number
                var rv = ua.indexOf('rv:');
                return true;
            }

            var edge = ua.indexOf('Edge/');
            if (edge > 0) {
               // Edge (IE 12+) => return version number
                return true;
            }

            // other browser
            return false;
        },
    /**
     * Common utility for sending event notifications through the tunnel.
     * @param {String} node
     *     The node that the event was published on
     * @param {String} payload
     *     The payload of the notification
     * @private
     */
	_sendEvent = function (node, payload) {
		//Since the node path matches the REST URL, URI encoding/decoding should keep it safe.
		node = encodeURI(node ? node : "");
		payload = (payload ? payload : "");

		//We are sending the node path string concatenated before the XML update event:
		// '/finesse/api/User/1015<Update>...</Update>'		
		_sendMessage(_TYPES.EVENT, node + payload);
	},
    
    
    /**
     * The Websocket event handler IMPLEMENTATION, which consumes the event and publishes it to the
     * parent frame.
     * @param {Object} event
     *     The event object for the notification as given by strophe
     * @private
     */
    eventHandlerImpl = function (msgElement) {
        
        if (msgElement === null) {
            _log("EventTunnel.eventHandlerImpl() - recieved an event with null event");
            return true;
        }
        
        var messageText = msgElement.textContent,
            to = msgElement.getAttribute('to'),
            //We need to extract the node path and sent it back to MasterTunnel/MasterPublisher
            items = msgElement.getElementsByTagName('items')[0];
        
        if (messageText === null || to === null || items === null) { 
            _log("EventTunnel.eventHandlerImpl() -  - received an event with null text/to/items");
            return true;
        }
        
        _log("EventTunnel.eventHandlerImpl() - Event received::" + messageText);
        
        var node = items.getAttribute('node');
        
        if (node === null) {
            _log("EventTunnel.eventHandlerImpl() - Node info not present - cannot send message " + messageText);
            return true;
        }
        
		_sendEvent(node, messageText);
        
        //need to return true else this callback will not be called again
        return true;
    },


    /**
     * The Websocket event handler, which consumes the event and publishes it to the
     * parent frame.
     * @param {Object} event
     *     The event object for the notification as given by strophe
     * @private
     */
    _eventHandler = function (msgElement) { 
        try {
            return eventHandlerImpl(msgElement);
        } catch (e) { 
            _log("EventTunnel._eventHandler() - exception in event handling .. " + e.stack);
        }
        return true;
    },


    /**
     * Disconnects the Websocket connection
     * @private
     */
	_disconnect = function () {
		if (_xmppClient) {
            _log("EventTunnel._disconnect() - disconnect requested ...");
			_xmppClient.disconnect('Requested to disconnect');
		}
	},
	
    /**
     * Iterates through all nodes with active subscriptions and unsubscribes from them
     * @private
     */
    
	_unsubscribeAllNodes = function () {	
		_pubsubNodes.forEach(	
		   function (node) {
			    _unsubscribe(node);
		});
	},
	


    /**
     * Utility to unsubscribe from all nodes and disconnect the Websocket session
     * @private
     */
    _cleanupSession = function () {
        //Tell clients that we are unloading the page
        _sendMessage(_TYPES.STATUS, _STATUS[6]);
        _unsubscribeAllNodes();        
        //We may want to consider moving this before destruction if it becomes a problem; not sure if destroy will work after disconnect.
        _disconnect();
    },

    /**
     * Utility to clean everything up upon unloading
     * @private
     */
    _unload = function () {
        _cleanupSession();
    },
	
	/**
     * Checks to see whether the strophe client is both connected and the
     * connectedUser has established their available presence to the openfire
     * server. If so, the "connected" status for the Websocket connection will be
     * sent back to the parent frame.
     * 
     * @private
     */
	_checkToSendConnected = function () {
        _log("EventTunnel._checkToSendConnected(): status=" + _xmppClientStatus + ", _initPresence=" + _initPresence);
        if (_xmppClientStatus !== undefined && _xmppClientStatus === Strophe.Status.CONNECTED && _initPresence === true) {
            _log("EventTunnel._checkToSendConnected(): sending connected");
            _sendMessage(_TYPES.RESOURCEID, _xmppResource);
            _sendMessage(_TYPES.STATUS, "connected");
        }
    },
	
    
    /**
     * Called by the presence handler. This function will determine whether the
     * jid belongs to the "finesse" xmpp user and if so, set the _initPresence
     * flag to true to indicate that the strophe client's connectedUser has
     * successfully set their presence to available. This is a workaround
     * because at this time, Openfire 3.7.0 does not support the latest spec on
     * IM and presence (RFC 6121) which states that when the xmpp server
     * receives initial presence, it should send that presence back to the
     * client. In other words, since Openfire sends the presence of subscribed
     * users upon initial presence being received, that mechanism is being used
     * to indicate that the initial presence has been received by Openfire.
     * 
     * @param {String}
     *            jid The full jid of the user that sent their presence.
     * @private
     */
    _checkFinesseUser = function (jid) {
        var user,
        index = jid.indexOf("@");
        
        if (index > 0) {
            user = jid.substr(0, index);
            // If presence is for Finesse user, set initPresence to true
            if (user === "finesse") {
                _initPresence = true;
            } else if (user.indexOf("cuic.") > -1 || user.indexOf("ccx.") > -1) {
                //Need to initPresence for CUIC and CCX
                _initPresence = true;
            }
        }
    },    
    
    /**
     * The presence handler Implementation, which consumes the presence event and
     * publishes the presence to the parent frame.
     * @param {Object} event
     *     The presence update event.
     * @private
     */
    _presenceHandlerImpl = function (msgElement) {
        
        _log("EventTunnel._presenceHandlerImpl() - receieved presence message .."+msgElement);
        
        if (msgElement === null) { 
            return true;
        }
        
        var from = msgElement.getAttribute('from');
        var type = msgElement.getAttribute('type');
        
        if (from === null) { 
            _log("EventTunnel._presenceHandlerImpl()  - could not handle presence message since from is null..");
            return true;
        }
        
        
        _log("EventTunnel._presenceHandlerImpl()  - receieved presence message .." + "from:" + from + "type:" + type);
        
        // Only check the following during the init phase of the
        // desktop, once initial presence has been confirmed, disable
        // this check
        if (!_initPresence) {
            _checkFinesseUser(from);
            _checkToSendConnected();
        }
        

        var presence = {
            from: from,
            type: type
        };
        
        var presenceObject = {"presence":presence};
        
        presenceXml = finesse.Converter.json2xml(presenceObject);
        
        if (presenceXml) {
             _log("EventTunnel._presenceHandlerImpl() - broacasting presence message .." +  presenceXml);
            _sendMessage(_TYPES.PRESENCE, presenceXml);
        }
        
        //need to return true else this callback will not be called again
        return true;
    },

    /**
     * The presence handler, which consumes the presence event and
     * publishes the presence to the parent frame.
     * @param {Object} event
     *     The presence update event.
     * @private
     */
     
    _presenceHandler = function (msgElement) {
        
         try
        {
           return _presenceHandlerImpl(msgElement);
        }
        catch (e) { 
            _log("EventTunnel._presenceHandler() - exception in event handling of presence .. " + e.stack);
        }
        
        return true;
    }, 
     
    _pingSuccess = function(data) {
        _pingCounter = 0; 
        //_log('EventTunnel._pingSuccess - Ping response was successful.'); 
    },
    
    _pingError = function (error) {
        if (_pingCounter < _xmppProperties.xmppFailoverRequestMaxRetry) {
            _ping();
        }
        _log('EventTunnel._pingError - Ping response was unsuccessful.' + JSON.stringify(error));
    },
    
    _ping = function () {
        _pingCounter++;
        try {
            _xmppClient.ping.ping(_xmppDomain, _pingSuccess, _pingError, _xmppProperties.xmppRequestTimeout); 
        } catch (error) {
            _pingCounter = _xmppProperties.xmppFailoverRequestMaxRetry;
        }
        if (_pingCounter ===  _xmppProperties.xmppFailoverRequestMaxRetry) {
            _onConnect(Strophe.Status.DISCONNECTED);
        }
    },
    
    /**
    * start a custom ping to openfire, this is required becuase when network disconnect happens the websocket connection
    * is not throwing a excception or getting closed. the logic here takes cares of this scenario. We start a custom ping and
    * wait for succesful ping response, if there is succcesful response we send the next ping and so on. if there was no response
    * for a ping we check for two unsuccesful pings and closed the websocket connection and failover is triggered.
    */
    _startPing = function () {
       _pingCounter = 0;
       clearInterval(_pingIntervalHandler);
       _pingIntervalHandler = setInterval( _ping, _xmppProperties.xmppFailoverDetectionPingInterval);
    },
    
    _resetConnection = function() {
        if(_xmppClient) {
	        _xmppClient.reset();
        }
	
        clearInterval(_pingIntervalHandler);
        _pingIntervalHandler = null;
    },
    
    _onConnect = function (status,errorCondition) {

        _log("EventTunnel._onConnect() - XMPP client onCONNECT fired");

        var unloadEvent = (_isIE) ? "unload" : "beforeunload";
        var statusStr;

        _isConnected = false;

        _log("EventTunnel._onConnect() - XMPP client onConnect status is: " + status + ":"+errorCondition);

        // THESE STATUS CODES ARE SELF EXPLANATORY
        if (status === Strophe.Status.ERROR && errorCondition === "conflict") {
           statusStr = "conflict";
           _initPresence = false;
           _log("EventTunnel._onConnect() - XMPP client about to reset because of status:" + statusStr);
          _resetConnection();
	}
        else if (status === Strophe.Status.AUTHFAIL) {
           statusStr = "unauthorized";
           _initPresence = false;
           _log("EventTunnel._onConnect() - XMPP client about to reset because of status:" + statusStr);
            _resetConnection();
	 }
	 else if (status === Strophe.Status.CONNECTING) {
	    _xmppClientStatus = Strophe.Status.CONNECTING;
	 } else if (status === Strophe.Status.CONNFAIL) {
	    _xmppClientStatus = Strophe.Status.CONNFAIL;
	 } else if (status === Strophe.Status.DISCONNECTING) {
	    _xmppClientStatus = Strophe.Status.DISCONNECTING;
	 } else if (status === Strophe.Status.DISCONNECTED) {
	    statusStr = "disconnected";
            _xmppClientStatus = Strophe.Status.DISCONNECTED;
            window.removeEventListener(unloadEvent, _unload);
            _initPresence = false;
            _log("EventTunnel._onConnect() - XMPP client about to reset because of status:" + statusStr);
            _resetConnection();
	 } else if (status === Strophe.Status.CONNECTED) {
	    statusStr = "connected";
	    _xmppClientStatus = Strophe.Status.CONNECTED;
            window.addEventListener(unloadEvent, _unload);
	    // We add a listener that will catch the opposite user's msgs
	    _xmppClient.addHandler(_eventHandler, null, 'message', null, null,  null); 
	    _xmppClient.addHandler(_presenceHandler, null, 'presence', null, null,  null);    
            if (_notificationConnectionType.toLowerCase() === "websocket") {	       
	        _startPing();
            }
	    // We send online presense to the server. (pub sub concept)
	    //We must send a presence when the connection's status is  Strophe.Status.CONNECTING
	    _xmppClient.send($pres().tree());
            // Do not send the connected status immediately. The
            // connected status is gated on the strophe client's
            // connectedUser presence because OpenFire will not route events to
            // the session for this user unless their presence is available.
            _checkToSendConnected();            
            // Set to undefined so that it will not be sent to the
            // parent frame just yet.
            statusStr = undefined;
            _isConnected = true;
	}
    
	//Send the resource ID and the new connection status to parent frame.
        if (statusStr) {
            _sendMessage(_TYPES.RESOURCEID, _xmppResource);
            _sendMessage(_TYPES.STATUS, statusStr);
        }
        
        return true;

    },


    /**
     * Get's the list of subscriptions to other nodes.
     * @return
     * JSON Array with objects like below: 
     *  
     * <pre>
     *  {
     *        "node": "/finesse/api/User/1001050/Media",
     *        "jid": "<userid>@<host>",
     *        "status": "subscribed"
     *   }
     * </pre>
     */
    _subscriptionsReq = function() {
        var successCallback = function(resp) {
            var associatedNodes = resp.getElementsByTagName('subscriptions')[0].childNodes;

            var defaultSubscriptions = [];

            associatedNodes.forEach(function(sub) {
                defaultSubscriptions.push(
                        {
                            'node': sub.getAttribute('node'), // Subscribed 'to' target node
                            'jid': sub.getAttribute('jid'), // JID of the node which had subscribed to target node
                            'status': sub.getAttribute('subscription') // should be "subscribed"
                        }
                    );
            });

            //_log("EventTunnel._subscriptionsReq() succ cb. returning :" + JSON.stringify(defaultSubscriptions,null,2));
            _sendMessage(_TYPES.SUBSCRIPTIONS_REQ, defaultSubscriptions);
        };

        var errorCallback = function(resp) {
            //_log("EventTunnel._subscriptionsReq() err cb. unable to get subscriptions .. " + resp);
            _sendMessage(_TYPES.SUBSCRIPTIONS_REQ, resp+"|<ApiErrors/>");
        };

        _xmppClient.pubsubext.subscriptions('to', successCallback, errorCallback);
    },
    
    /**
     * Establish websocket connection using strophe library.
     * @param {String} ID
     *     The ID of the user configured on the XMPP notification server.
     * @param {String} password
     *     The password belonging to the user.
     * @param {String} domain
     *     The domain of the notification server (i.e. subdomain.host.com)
     * @param {String} [resource]
     *     The resource ID of the user's device used to log in. The ID will be
     *     auto-generated if none is specified.
     * @param {String} notificationConnectionType
     *     The XMPP connection protocol : websocket or BOSH
     * @private
     */
    _connect = function (ID, password, domain, resource, notificationConnectionType) {
        ID = ID.toLowerCase();
        _log("EventTunnel.connect() - ID:"+ ID +", domain:"+domain+", resource:"+ resource);

        //Construct JID with username and domain.
        var  jid = ID + "@" + domain + "/" + resource,
         scheme = "",
         bindURL = "";
        _log("EventTunnel.connect() - XMPP client JID for connection = "+ jid);
         
         if (notificationConnectionType.toLowerCase() === "bosh") {
             scheme = window.location.protocol;
             bindURL = "/http-bind/";
         } else {
             // Else fallback to default websocket
             scheme = window.location.protocol === "https:" ? "wss:" : "ws:";
             bindURL = "/ws/";
         }
         var connectURL = scheme + "//" + window.location.host + bindURL;
         _log("EventTunnel.connect() - XMPP client connect url = " + connectURL);
            

        if (_xmppClient) {
            _log("EventTunnel.connect() - XMPP client about to CONNECT..Found existing tunnel - about to kill them");
            _xmppClient.disconnect();
            _xmppClient.reset();
        }

        _xmppResource = resource;
        
        _log("EventTunnel.connect() - Initialize Strophe XMPP client");        
        _xmppClient = new Strophe.Connection(connectURL);
        _log("EventTunnel.connect() - Strophe XMPP client created");     
       
       _log("EventTunnel.connect() - Calling Strophe XMPP connect");
       //Connect to Websocket connection.
       _xmppClient.connect(jid, password, _onConnect);
       
    },

    /**
     * Utility for sending a subscription request to the XMPP notification server.
     * This is likely invoked by a _TYPES.SUBSCRIBE message and responds with the same.
     * @param {String} node
     *     The path of the node of interest to be subscribed
     * @private
     */
	_subscribe = function (node) {
        // first make sure we are in connected state
        if (!_isConnected) {
            _sendMessage(_TYPES.SUBSCRIBE, node + "|<ApiErrors/>");
            return;
        }

		if (_pubsubDomain) {
            _xmppClient.pubsub.subscribe(
				_xmppClient.jid,
				_pubsubDomain,
				node,
				[],
				function () {

				},
				function () {
					var msg = node;
					_pubsubNodes.push(node);
					_sendMessage(_TYPES.SUBSCRIBE, msg);
				}
			);
		}
	},

    /**
     * Utility for sending an unsubscribe request to the XMPP notification server.
     * This is likely invoked by a _TYPES.UNSUBSCRIBE message and responds with the same.
     * @param {String} node
     *     The path of the node of interest to be unsubscribed
     * @private
     */
	_unsubscribe = function (node) {
        // first make sure we are in connected state
        if (!_isConnected) {
            _sendMessage(_TYPES.UNSUBSCRIBE, node + "|<ApiErrors/>");
            return;
        }
        
        _xmppClient.pubsub.unsubscribe(_xmppClient.jid, _pubsubDomain, node, function() {
         _log("EventTunnel._unsubscribe() request on node"+ node + "was successful");    
         //_pubsubNodes[node].destroy();
         delete _pubsubNodes[node];
         _sendMessage(_TYPES.UNSUBSCRIBE, node);
        });
    },
    
    /**
     * Updating properties as per set in desktop properties , configurable through cfadmin
     * and admin CLI property change
     */
    _populateXmppProperties = function(xmppPropertiesStringified) {
        var xmppProperties = JSON.parse(xmppPropertiesStringified);
        _xmppProperties.xmppFailoverRequestMaxRetry =  parseInt(xmppProperties.xmppFailoverRequestMaxRetry,10);
        _xmppProperties.xmppFailoverDetectionPingInterval = parseInt(xmppProperties.xmppFailoverDetectionPingInterval,10);
        _xmppProperties.xmppRequestTimeout = parseInt(xmppProperties.xmppRequestTimeout,10);
    },
	
	/**
     * Method to attempt to establish a Websocket connection with the XMPP server through strophe
     * @param {String} connInfo
     *     xml string describing a connInfo object containing id, password, and xmppDomain elements
     * @private
     */
	_processConnectReq = function (connInfo) {
        // Convert connInfo to json obj
        var connInfoObj = JSON.parse(finesse.Converter.xml2json(window.DOMParser().parseFromString(connInfo, "text/xml"), ""));
        _connect(connInfoObj.connInfo.id, connInfoObj.connInfo.password, connInfoObj.connInfo.xmppDomain, _resource, connInfoObj.connInfo.notificationConnectionType);
	},
	
    /**
     * Handler for messages delivered by window.postMessage. Listens for
     * credentials to be passed by parent frame in order to establish a bosh/Websocket
     * connection.
     * @param {Object} e
     *     The message object as provided by the window.postMessage feature.
     * @private
     */
    _messageHandler = function (e) {
        var

        //Extract the message type and message data. The expected format is
        //"type|data" where type is a number represented by the TYPES object.
        delimPos = e.data.indexOf("|"),
        type = Number(e.data.substr(0, delimPos)),
        data =  e.data.substr(delimPos + 1);

        //Since the ID and password is being delivered by the parent frame
        //separately, store the credentials until both fields come in
        //before attempting to connect.

		switch (type) {
        case _TYPES.ID:
            _id = data;
            break;
        case _TYPES.XMPPDOMAIN:
            _xmppDomain = data;
            break;
        case _TYPES.PASSWORD:
            _password = data;
            break;
        case _TYPES.RESOURCEID:
            _resource = data;
            break;
        case _TYPES.PUBSUBDOMAIN:
            _pubsubDomain = data;
            return;
        case _TYPES.SUBSCRIBE:
            _subscribe(data);
            return;
        case _TYPES.UNSUBSCRIBE:
            _unsubscribe(data);
            return;
        case _TYPES.SUBSCRIPTIONS_REQ:
            _subscriptionsReq();
            return;
        case _TYPES.CONNECT_REQ:
            _processConnectReq(data);
            return;
        case _TYPES.DISCONNECT_REQ:
            _unload();
            return;
        case _TYPES.NOTIFICATION_CONNECTION_TYPE:
            _notificationConnectionType = data;
            break;
        case _TYPES.XMPP_DISCONNECT_PROPERTIES:
            _populateXmppProperties(data);
            break;
            
        }

        //Ensure that ID, domain and password credentials have been received
        //before attempting to establish a Websocket connection.
        if (_id !== undefined && _password !== undefined && _xmppDomain !== undefined && _notificationConnectionType !== undefined) {
            try {
                _connect(_id, _password, _xmppDomain, _resource, _notificationConnectionType);
            } catch (err) {
                _log(err);
            }

            //Remove reference to password.
            _password = undefined;
        }
    };
    
    /**
     * Initiate the message listener to wait for actions from the parent frame.
     */
    this.init = function () {
        // Determine whether the we're running in an Internet Explorer
        // browser. Flag is used for disconnect logic which is browser
        // dependent.
        _isIE = _isInternetExplorer(); //window.navigator.userAgent.indexOf("MSIE") !== -1;

        _util.receiveMessage(_messageHandler);

        //Send a "loaded" status message to indicate to the parent frame to
        //send domains/credentials.
        _sendMessage(_TYPES.STATUS, _STATUS[0]);
    };

    //BEGIN TEST CODE//
    /**
     * Test code added to expose private functions that are used by unit test
     * framework. This section of code is removed during the build process
     * before packaging production code. The [begin|end]TestSection are used
     * by the build to identify the section to strip.
     * @ignore
     */
    this.beginTestSection = 0;

    /**
     * @ignore
     */
    this.getTestObject = function () {
        //Load mock dependencies.
        var _mock = new MockControl();
        _util = _mock.createMock(finesse.EventTunnel.Utilities);

        return {
            //Expose mock dependencies
            mock: _mock,
            util: _util,

            //Expose internal private functions
            jwClient: _jwClient,
            types: _TYPES,
            sendMessage: _sendMessage,
            eventHandler: _eventHandler,
            connect: _connect,
            setConnect: function (connect) {
                _connect = connect;
            },
            messageHandler: _messageHandler
        };
    };

    /**
     * @ignore
     */
    this.endTestSection = 0;
    //END TEST CODE//
};

finesse.EventTunnel.Utilities = (function () {
    return {
        /**
         * Creates a message listener for window.postMessage messages.
         * @param {Function} callback
         *     The callback that will be invoked with the message. The callback
         *     is responsible for any security checks.
         * @param {String} [origin]
         *     The origin to check against for security. Allows all messages
         *     if no origin is provided.
         * @returns {Function}
         *     The callback function used to register with the message listener.
         *     This is different than the one provided as a parameter because
         *     the function is overloaded with origin checks.
         * @throws {Error} If the callback provided is not a function.
         */
        receiveMessage: function (callback, origin) {
            if (typeof callback !== "function") {
                throw new Error("Callback is not a function.");
            }

            //Create a function closure to perform origin check.
            var cb = function (e) {
				// If an origin check is requested (provided), we'll only invoke the callback if it passes
                if (typeof origin !== "string" || (typeof origin === "string" && typeof e.origin === "string" && e.origin.toLowerCase() === origin.toLowerCase())) {
                    callback(e);
                }
            };

            if (window.addEventListener) { //Firefox, Opera, Chrome, Safari
                window.addEventListener("message", cb, false);
            } else { //Internet Explorer
                window.attachEvent("onmessage", cb);
            }

            //Return callback used to register with listener so that invoker
            //could use it to remove.
            return cb;
        },

        /**
         * Sends a message to a target frame using window.postMessage.
         * @param {Function} message
         *     Message to be sent to target frame.
         * @param {Object} [target="parent"]
         *     An object reference to the target frame. Default us the parent.
         * @param {String} [targetOrigin="*"]
         *     The URL of the frame this frame is sending the message to.
         */
        sendMessage: function (message, target, targetOrigin) {
            //Default to any target URL if none is specified.
            targetOrigin = targetOrigin || "*";

            //Default to parent target if none is specified.
            target = target || parent;

            //Ensure postMessage is supported by browser before invoking.
            if (window.postMessage) {
                target.postMessage(message, targetOrigin);
            }
        }
    };
}());
EventTunnel.js
Displaying EventTunnel.js.