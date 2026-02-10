<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.model.Ruolo" %>
<%@ page import="it.unisa.uniclass.conversazioni.model.Messaggio" %>
<%@ page import="java.util.List" %>
<%@ page import="java.util.ArrayList" %>

<%
    /* Sessione HTTP */
    HttpSession sessione = request.getSession(false);
    if (sessione == null || sessione.getAttribute("currentSessionUser") == null) {
        response.sendRedirect("Login.jsp");
        return;
    }

    Utente user = (Utente) sessione.getAttribute("currentSessionUser");

    /* Verifica Accesso: Solo Accademici */
    if (!(user instanceof Accademico)) {
        response.sendRedirect("ErroreAccesso.jsp");
        return;
    }

    Accademico accademicoLoggato = (Accademico) user;

    // Recupero attributi passati dalla Servlet
    Accademico interlocutore = (Accademico) request.getAttribute("accademico"); // "accademico" nel controller era l'altro
    if (interlocutore == null) {
        // Fallback sessione se request è vuota (per compatibilità col vecchio codice)
        interlocutore = (Accademico) session.getAttribute("accademico");
    }

    List<Messaggio> messaggigi = (List<Messaggio>) request.getAttribute("messaggigi");
    if (messaggigi == null) {
        messaggigi = (List<Messaggio>) session.getAttribute("messaggigi"); // Fallback
    }
    if (messaggigi == null) messaggigi = new ArrayList<>();
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
        <% if (accademicoLoggato.getRuolo() == Ruolo.STUDENTE) { %>
        <li id="orari"><a href="servelt">Orari</a></li>
        <% } %>
        <li id="aule"><a href="AulaServlet">Aule</a></li>
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
        <h2>
            <% if (interlocutore != null) { %>
            Chat con: <%= interlocutore.getNome() %> <%= interlocutore.getCognome() %>
            <% } else { %>
            Seleziona un utente
            <% } %>
        </h2>
    </div>

    <div id="chat-box" class="chat-box">
        <%
            if (interlocutore != null) {
                for (Messaggio messaggio : messaggigi) {

                    // Controllo Topic
                    if (messaggio.getTopic() != null && !"VUOTO".equals(messaggio.getTopic().getNome())) {
        %>
        <div class="message red-text">
            <span class="message-text">[<%= messaggio.getTopic().getNome()%>]</span>
        </div>
        <%
            }

            // Determina classe CSS (self vs author)
            String cssClass = "author";
            if (messaggio.getAutore() != null &&
                    messaggio.getAutore().getEmail().equals(accademicoLoggato.getEmail())) {
                cssClass = "self";
            } else if (messaggio.getAutore() != null &&
                    messaggio.getAutore().getEmail().equals(interlocutore.getEmail())) {
                cssClass = "author";
            } else {
                // Messaggio non pertinente a questa conversazione specifica, salto
                continue;
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
        <label for="testo" style="display:none;">Messaggio</label>
        <input type="text" id="testo" name="testo" class="chat-input" placeholder="Scrivi un messaggio..." required>

        <% if (interlocutore != null) { %>
        <input type="hidden" id="emailInvio" name="emailInvio" value="<%= interlocutore.getEmail() %>">
        <% } %>

        <button type="button" class="send-button" onclick="sendMessage()">Invia</button>
    </div>
</div>

<script>
    function sendMessage() {
        var testo = document.getElementById('testo').value;
        var emailInvioElem = document.getElementById('emailInvio');

        if (!emailInvioElem) {
            alert("Nessun destinatario selezionato");
            return;
        }

        var email = emailInvioElem.value;
        if(testo.trim() !== "") {
            // Assicurati che l'URL punti alla servlet corretta refactorizzata
            window.location.href = 'inviaMessaggioChatServlet?testo=' + encodeURIComponent(testo) + '&emailInvio=' + encodeURIComponent(email);
        }
    }

    document.getElementById("testo").addEventListener("keypress", function(event) {
        if (event.key === "Enter") {
            event.preventDefault();
            sendMessage();
        }
    });
</script>

</body>
</html>