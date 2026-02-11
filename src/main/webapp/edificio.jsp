<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>

<%@ page import="it.unisa.uniclass.utenti.model.Utente, it.unisa.uniclass.utenti.model.Tipo" %>
<%@ page import="it.unisa.uniclass.orari.model.Lezione" %>
<%@ page import="it.unisa.uniclass.orari.model.Aula" %>
<%@ page import="java.util.*" %>
<%@ page import="java.time.LocalDate" %>
<%@ page import="java.time.LocalTime" %>
<%@ page import="java.time.format.TextStyle" %>

<%
    HttpSession sessione = request.getSession(true);
    Utente user = (Utente) sessione.getAttribute("currentSessionUser");
    if (user != null) {
        session.setAttribute("utenteEmail", user.getEmail());
    }

    Tipo tipoUtente = (user != null) ? (Tipo) user.getTipo() : null;

    List<Aula> aule = (List<Aula>) request.getAttribute("aule");
    Map<String, List<Lezione>> lezioniPerAula =
            (Map<String, List<Lezione>>) request.getAttribute("lezioniPerAula");

    String edificio = (String) request.getAttribute("ed");
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">
<head>
    <title>Edificio</title>
    <script src="scripts/sidebar.js" type="text/javascript"></script>
    <link type="text/css" rel="stylesheet" href="styles/headerStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/formcss.css"/>
    <link type="text/css" rel="stylesheet" href="styles/footerstyle.css">
    <link type="text/css" rel="stylesheet" href="styles/edificiostyle.css">
    <link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
</head>
<body>

<div class="barraNavigazione" id="barraNavigazione">
    <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
        <img src="images/icons/menuOpenIcon.png" alt="closebtn">
    </a>
    <p>Menu</p>
    <ul id="menu">
        <li id="aule"><a href="AulaServlet">Aule</a></li>

        <% if (tipoUtente != null) { %>
        <% if (tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li id="gutenti"><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
        <% } else if (tipoUtente.equals(Tipo.Accademico)) { %>
        <li id="conversazioni"><a href="Conversazioni">Conversazioni</a></li>
        <% } %>
        <% } %>

        <li id="mappa"><a href="mappa.jsp">Mappa</a></li>
        <li id="ChatBot"><a href="ChatBot.jsp">ChatBot</a></li>
        <li id="infoapp"><a href="infoapp.jsp">Info App</a></li>
        <li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
    </ul>
</div>

<jsp:include page="header.jsp"/>
<br><br>

<h1>Edificio <%= edificio != null ? edificio : "" %></h1>

<ul class="buildings">
    <%
        if (aule != null) {

            LocalTime oraCorrente = LocalTime.now();
            LocalDate oggi = LocalDate.now();
            String giornoCorrente = oggi.getDayOfWeek().getDisplayName(TextStyle.FULL, Locale.ITALY);
            String giornoCorrenteMaiuscolo = giornoCorrente.replace("è", "e").replace("ì", "i").toUpperCase(Locale.ITALY);

            for (Aula aula : aule) {

                boolean occ = false;
                List<Lezione> lezioni = (lezioniPerAula != null)
                        ? lezioniPerAula.get(aula.getNome())
                        : null;

                if (lezioni != null) {

                    lezioni.sort((l1, l2) -> {
                        String g1 = (l1.getGiorno() != null) ? l1.getGiorno().toString() : "";
                        String g2 = (l2.getGiorno() != null) ? l2.getGiorno().toString() : "";
                        int cmp = g1.compareTo(g2);
                        if (cmp != 0) return cmp;

                        LocalTime o1 = (l1.getOraInizio() != null) ? l1.getOraInizio().toLocalTime() : LocalTime.MIN;
                        LocalTime o2 = (l2.getOraInizio() != null) ? l2.getOraInizio().toLocalTime() : LocalTime.MIN;
                        return o1.compareTo(o2);
                    });

                    for (Lezione lezione : lezioni) {
                        if (lezione.getGiorno() != null &&
                                giornoCorrenteMaiuscolo.equals(lezione.getGiorno().toString())) {

                            if (lezione.getOraInizio() != null && lezione.getOraFine() != null) {
                                LocalTime oraInizio = lezione.getOraInizio().toLocalTime();
                                LocalTime oraFine = lezione.getOraFine().toLocalTime();

                                if (oraCorrente.isAfter(oraInizio) && oraCorrente.isBefore(oraFine)) {
                                    occ = true;
                                    break;
                                }
                            }
                        }
                    }
                }
    %>

    <li class="building">
        <% if (occ) { %>
        <img class="imgOcc" src="images/icons/aulaOccupata.png" alt="Occupata">
        <% } else { %>
        <img class="imgOcc" src="images/icons/aulaLibera.png" alt="Libera">
        <% } %>

        <%= aula.getNome() %>

        <ul class="classes">
            <%
                if (lezioni != null) {
                    for (Lezione lezione : lezioni) {

                        if (lezione.getAula() == null ||
                                lezione.getAula().getNome() == null ||
                                !lezione.getAula().getNome().equals(aula.getNome())) continue;

                        String giorno = (lezione.getGiorno() != null) ? lezione.getGiorno().toString() : "N/D";
                        String oraInizio = (lezione.getOraInizio() != null) ? lezione.getOraInizio().toString() : "N/D";
                        String oraFine = (lezione.getOraFine() != null) ? lezione.getOraFine().toString() : "N/D";

                        String nomeCorso = (lezione.getCorso() != null) ? lezione.getCorso().getNome() : "N/D";
                        String anno = (lezione.getCorso() != null &&
                                lezione.getCorso().getAnnoDidattico() != null)
                                ? lezione.getCorso().getAnnoDidattico().getAnno()
                                : "N/D";

                        String resto = (lezione.getResto() != null) ? lezione.getResto().getNome() : "";
            %>

            <li class="occupata">
                <%= giorno %> —
                <%= oraInizio %> → <%= oraFine %> —
                <%= nomeCorso %> —
                <%= anno %> —
                <%= resto %>
            </li>

            <%
                    }
                }
            %>
        </ul>
    </li>

    <%
            } // fine for aule
        } // fine if aule
    %>
</ul>

<script>
    document.querySelectorAll('.building').forEach(building => {
        building.addEventListener('click', () => {
            const classes = building.querySelector('.classes');
            if (classes) {
                classes.style.display = classes.style.display === 'none' || classes.style.display === '' ? 'block' : 'none';
            }
        });
    });
</script>

<br><br><br>
<%@include file="footer.jsp" %>
</body>
</html>
