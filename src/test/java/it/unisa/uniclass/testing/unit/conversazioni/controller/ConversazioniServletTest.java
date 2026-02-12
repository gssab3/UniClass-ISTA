package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.ConversazioniServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

class ConversazioniServletTest {

    @Mock
    private HttpServletRequest request;
    @Mock
    private HttpServletResponse response;
    @Mock
    private HttpSession session;
    @Mock
    private MessaggioService messaggioService;
    @Mock
    private UserDirectory userDirectory;
    @Mock
    private RequestDispatcher requestDispatcher;

    private ConversazioniServlet servlet;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        servlet = new ConversazioniServlet();
        servlet.mockMessaggioService(messaggioService);
        servlet.mockUserDirectory(userDirectory);
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));
    }

    @Test
    void testDoPostWithStudentUser() throws Exception {
        String email = "studente@studenti.unisa.it";
        String matricola = "0512100001";

        Accademico studente = new Accademico();
        studente.setEmail(email);
        studente.setMatricola(matricola);
        studente.setNome("Mario");
        studente.setCognome("Rossi");
        studente.setRuolo(Ruolo.STUDENTE);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);
        when(userDirectory.getAccademico(email)).thenReturn(studente);

        List<Messaggio> messaggiRicevuti = new ArrayList<>();
        Messaggio msgRicevuto = new Messaggio();
        msgRicevuto.setBody("Ciao, come stai?");
        msgRicevuto.setDateTime(LocalDateTime.now());
        messaggiRicevuti.add(msgRicevuto);

        List<Messaggio> messaggiInviati = new ArrayList<>();
        Messaggio msgInviato = new Messaggio();
        msgInviato.setBody("Tutto bene, grazie!");
        msgInviato.setDateTime(LocalDateTime.now());
        messaggiInviati.add(msgInviato);

        List<Messaggio> avvisi = new ArrayList<>();
        Messaggio avviso = new Messaggio();
        avviso.setBody("Avviso importante");
        Topic topic = new Topic();
        topic.setNome("Topic1");
        avviso.setTopic(topic);
        avvisi.add(avviso);

        when(messaggioService.trovaMessaggiRicevuti(matricola)).thenReturn(messaggiRicevuti);
        when(messaggioService.trovaMessaggiInviati(matricola)).thenReturn(messaggiInviati);
        when(messaggioService.trovaAvvisi()).thenReturn(avvisi);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
        verify(request).setAttribute(eq("messaggiRicevuti"), eq(messaggiRicevuti));
        verify(request).setAttribute(eq("messaggiInviati"), eq(messaggiInviati));
        verify(requestDispatcher).forward(request, response);
    }

    @Test
    void testDoPostWithDocenteUser() throws Exception {
        String email = "docente@unisa.it";
        String matricola = "0512100010";

        Accademico docente = new Accademico();
        docente.setEmail(email);
        docente.setMatricola(matricola);
        docente.setNome("Giuseppe");
        docente.setCognome("Verdi");
        docente.setRuolo(Ruolo.DOCENTE);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);
        when(userDirectory.getAccademico(email)).thenReturn(docente);

        List<Messaggio> messaggiRicevuti = new ArrayList<>();
        List<Messaggio> messaggiInviati = new ArrayList<>();
        List<Messaggio> avvisi = new ArrayList<>();

        when(messaggioService.trovaMessaggiRicevuti(matricola)).thenReturn(messaggiRicevuti);
        when(messaggioService.trovaMessaggiInviati(matricola)).thenReturn(messaggiInviati);
        when(messaggioService.trovaAvvisi()).thenReturn(avvisi);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
        verify(requestDispatcher).forward(request, response);
    }

    @Test
    void testDoPostWithMultipleMessages() throws Exception {
        String email = "utente@studenti.unisa.it";
        String matricola = "0512100020";

        Accademico studente = new Accademico();
        studente.setEmail(email);
        studente.setMatricola(matricola);
        studente.setRuolo(Ruolo.STUDENTE);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);
        when(userDirectory.getAccademico(email)).thenReturn(studente);

        List<Messaggio> messaggiRicevuti = new ArrayList<>();
        List<Messaggio> messaggiInviati = new ArrayList<>();
        List<Messaggio> avvisi = new ArrayList<>();

        for (int i = 0; i < 10; i++) {
            Messaggio msg1 = new Messaggio();
            msg1.setBody("Messaggio ricevuto " + i);
            messaggiRicevuti.add(msg1);

            Messaggio msg2 = new Messaggio();
            msg2.setBody("Messaggio inviato " + i);
            messaggiInviati.add(msg2);

            if (i < 5) {
                Messaggio av = new Messaggio();
                av.setBody("Avviso " + i);
                Topic t = new Topic();
                t.setNome("Topic" + i);
                av.setTopic(t);
                avvisi.add(av);
            }
        }

        when(messaggioService.trovaMessaggiRicevuti(matricola)).thenReturn(messaggiRicevuti);
        when(messaggioService.trovaMessaggiInviati(matricola)).thenReturn(messaggiInviati);
        when(messaggioService.trovaAvvisi()).thenReturn(avvisi);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
        verify(requestDispatcher).forward(request, response);
    }

    @Test
    void testDoPostWithEmptyLists() throws Exception {
        String email = "nuovo@studenti.unisa.it";
        String matricola = "0512100030";

        Accademico studente = new Accademico();
        studente.setEmail(email);
        studente.setMatricola(matricola);
        studente.setRuolo(Ruolo.STUDENTE);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);
        when(userDirectory.getAccademico(email)).thenReturn(studente);

        List<Messaggio> messaggiVuoti = new ArrayList<>();

        when(messaggioService.trovaMessaggiRicevuti(matricola)).thenReturn(messaggiVuoti);
        when(messaggioService.trovaMessaggiInviati(matricola)).thenReturn(messaggiVuoti);
        when(messaggioService.trovaAvvisi()).thenReturn(messaggiVuoti);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
        verify(requestDispatcher).forward(request, response);
    }

    @Test
    void testDoGet() throws Exception {
        String email = "test@studenti.unisa.it";
        String matricola = "0512100040";

        Accademico studente = new Accademico();
        studente.setEmail(email);
        studente.setMatricola(matricola);
        studente.setRuolo(Ruolo.STUDENTE);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);
        when(userDirectory.getAccademico(email)).thenReturn(studente);

        List<Messaggio> messaggiVuoti = new ArrayList<>();

        when(messaggioService.trovaMessaggiRicevuti(matricola)).thenReturn(messaggiVuoti);
        when(messaggioService.trovaMessaggiInviati(matricola)).thenReturn(messaggiVuoti);
        when(messaggioService.trovaAvvisi()).thenReturn(messaggiVuoti);

        servlet.doGet(request, response);

        verify(requestDispatcher).forward(request, response);
    }

    @Test
    void testDoPostWithNullSession() throws Exception {
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(null);

        servlet.doPost(request, response);

        verify(response).sendRedirect("Login.jsp");
    }

    @Test
    void testDoPostWithNonAccademico() throws Exception {
        String email = "admin@unisa.it";

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(userDirectory.getAccademico(email)).thenReturn(null);

        servlet.doPost(request, response);

        verify(response).sendError(HttpServletResponse.SC_FORBIDDEN, "Accesso consentito solo agli accademici.");
    }

    @Test
    void testDoPostWithDifferentEmailFormats() throws Exception {
        String email = "g.verdi@unisa.it";
        String matricola = "0512100060";

        Accademico docente = new Accademico();
        docente.setEmail(email);
        docente.setMatricola(matricola);
        docente.setNome("Giovanni");
        docente.setCognome("Verdi");
        docente.setRuolo(Ruolo.DOCENTE);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);
        when(userDirectory.getAccademico(email)).thenReturn(docente);

        List<Messaggio> messaggi = new ArrayList<>();

        when(messaggioService.trovaMessaggiRicevuti(matricola)).thenReturn(messaggi);
        when(messaggioService.trovaMessaggiInviati(matricola)).thenReturn(messaggi);
        when(messaggioService.trovaAvvisi()).thenReturn(messaggi);

        servlet.doPost(request, response);

        verify(messaggioService).trovaMessaggiRicevuti(matricola);
        verify(messaggioService).trovaMessaggiInviati(matricola);
        verify(requestDispatcher).forward(request, response);
    }
}
