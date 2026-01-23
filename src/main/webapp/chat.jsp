<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>

<%@ page import="it.unisa.uniclass.utenti.model.Utente, it.unisa.uniclass.utenti.model.Tipo" %>
<%@ page import="it.unisa.uniclass.orari.model.CorsoLaurea" %>
<%@ page import="java.util.List" %>
<%@ page import="it.unisa.uniclass.conversazioni.model.Messaggio" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.service.AccademicoService" %>
<%@ page import="java.util.ArrayList" %>

<%
    /* Sessione HTTP */
    HttpSession sessione = request.getSession(true);
    Utente user = (Utente) sessione.getAttribute("currentSessionUser");
    if(user != null){
        session.setAttribute("utenteEmail", user.getEmail());
    }

    /* Controllo tipo utente */
    Tipo tipoUtente = null;

    // Logica di accesso originale mantenuta
    if(user != null && ((user.getTipo() != Tipo.Docente) || (user.getTipo() != Tipo.Coordinatore) || (user.getTipo()) != Tipo.Studente)) {
        tipoUtente = (Tipo) user.getTipo();
    } else if (user != null && (user.getTipo() == Tipo.PersonaleTA)) {
        response.sendRedirect("ErroreAccesso.jsp");
        return;
    } else {
        response.sendRedirect("Login.jsp");
        return;
    }

    Long id = (Long) request.getAttribute("id");
    String email = (String) request.getAttribute("email");

    Accademico accademico = (Accademico) session.getAttribute("accademico");
    Accademico accademicoSelf = (Accademico) session.getAttribute("accademicoSelf");

    // Recupero messaggi dalla sessione (con fallback per evitare NullPointerException)
    List<Messaggio> messaggigi = (List<Messaggio>) session.getAttribute("messaggigi");
    if (messaggigi == null) {
        messaggigi = new ArrayList<Messaggio>();
    }

    List<Messaggio> messaggi = new ArrayList<Messaggio>();
    List<Messaggio> messaggiInviati;
    List<Messaggio> messaggiRicevuti;

    if (tipoUtente == Tipo.Docente || tipoUtente == Tipo.Studente || tipoUtente == Tipo.Coordinatore){
        messaggiInviati = (List<Messaggio>) request.getAttribute("messaggiInviati");
        messaggiRicevuti = (List<Messaggio>) request.getAttribute("messaggiRicevuti");
    }
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">

<head>
    <title>UniClass Chat</title>
    <script src="scripts/sidebar.js" type="text/javascript"></script>
    <link type="text/css" rel="stylesheet" href="styles/headerStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/chatCss.css">
    <link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
    <script src="https://code.jquery.com/jquery-3.6.4.min.js"></script>
</head>

<body>

<div class="barraNavigazione" id="barraNavigazione">
    <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
        <img src="images/icons/menuOpenIcon.png" alt="closebtn">
    </a>
    <p>Menu</p>
    <ul id="menu">

        <%-- Solo Studente vede Orari --%>
        <% if (tipoUtente != null && tipoUtente.equals(Tipo.Studente)) { %>
        <li id="orari"><a href="servelt">Orari</a></li>
        <% } %>

        <li id="aule"><a href="aula.jsp">Aule</a></li>
        <li id="conversazioni"><a href="Conversazioni">Conversazioni</a></li>
        <li id="mappa"><a href="mappa.jsp">Mappa</a></li>
        <li id="ChatBot"><a href="ChatBot.jsp">ChatBot</a></li>
        <li id="infoapp"><a href="infoapp.jsp">Info App</a></li>
        <li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
    </ul>
</div>

<jsp:include page="header.jsp"/>

<div class="chat-container">
    <div class="chat-header">
        <h2><%-- Nome Interlocutore opzionale qui --%></h2>
    </div>

    <div id="chat-box" class="chat-box">
        <%
            if (accademicoSelf != null && accademico != null) {
                for (Messaggio messaggio : messaggigi) {

                    // 1. Gestione Visualizzazione Topic (Opzionale)
                    if (messaggio.getTopic() != null && !messaggio.getTopic().getNome().equals("VUOTO")) {
        %>
        <div class="message red-text">
            <span class="message-text">[<%= messaggio.getTopic().getNome()%>]</span>
        </div>
        <%
            }

            // 2. Gestione Classe CSS (Self vs Author)
            String cssClass = "author"; // Default (messaggio ricevuto)
            if (messaggio.getAutore().getEmail().equals(accademicoSelf.getEmail())) {
                cssClass = "self"; // Messaggio inviato da me
            } else if (messaggio.getAutore().getEmail().equals(accademico.getEmail())) {
                cssClass = "author";
            } else {
                continue; // Salta messaggi non pertinenti alla coppia (sicurezza)
            }
        %>
        <div class="message <%= cssClass %>">
            <span class="message-text"><%= messaggio.getBody() %></span>
        </div>
        <%
                }
            }
        %>
    </div>

    <div class="chat-input-container">
        <label for="testo" style="display:none;">Messaggio</label> <%-- Label nascosta per accessibilità --%>
        <input type="text" id="testo" name="testo" class="chat-input" placeholder="Scrivi un messaggio..." required>

        <% if (accademico != null) { %>
        <input type="hidden" id="emailInvio" name="emailInvio" value="<%=accademico.getEmail()%>">
        <% } %>

        <button type="button" class="send-button" onclick="sendMessage()">Invia</button>
    </div>
</div>

<script>
    // Funzione helper per l'invio (più pulita dell'inline onclick)
    function sendMessage() {
        var testo = document.getElementById('testo').value;
        var email = document.getElementById('emailInvio').value;
        if(testo.trim() !== "") {
            window.location.href = 'inviaMessaggioChatServlet?testo=' + encodeURIComponent(testo) + '&emailInvio=' + encodeURIComponent(email);
        }
    }

    // Aggiunge supporto tasto Enter
    document.getElementById("testo").addEventListener("keypress", function(event) {
        if (event.key === "Enter") {
            event.preventDefault();
            sendMessage();
        }
    });
</script>

</body>
</html>