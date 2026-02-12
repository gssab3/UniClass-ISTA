package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.chatServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectoryImpl;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

class ChatServletTest {

    // 1. Mockiamo le dipendenze HTTP (la "finta" richiesta web)
    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private HttpSession session;

    // 2. Mockiamo i Service (il "finto" database)
    @Mock
    private MessaggioService messaggioService;

    @Mock
    private UserDirectoryImpl userDirectoryImpl;

    // 3. La servlet vera che verrà testata
    private chatServlet servlet;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        servlet = new chatServlet();
        servlet.mockMessaggioService(messaggioService);
        servlet.mockUserDirectory(userDirectoryImpl);
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));
    }

    @Test
    void testDoGet() throws Exception {
        // --- ARRANGE (Preparazione dei dati finti) ---

        // Simuliamo le email passate come parametri dalla JSP
        String emailAltro = "professore@unisa.it";
        String emailSelf = "studente@studenti.unisa.it";
        String matricolaSelf = "0512100001";
        String matricolaAltro = "0512100002";

        when(request.getParameter("accademico")).thenReturn(emailAltro);
        when(request.getParameter("accademicoSelf")).thenReturn(emailSelf);
        when(request.getSession()).thenReturn(session);
        when(request.getContextPath()).thenReturn("/UniClass");

        // Creiamo gli oggetti Accademico finti
        Accademico self = new Accademico();
        self.setMatricola(matricolaSelf);
        self.setEmail(emailSelf);

        Accademico altro = new Accademico();
        altro.setMatricola(matricolaAltro);
        altro.setEmail(emailAltro);

        // Istruiamo il service mockato su cosa restituire
        when(accademicoService.trovaEmailUniClass(emailSelf)).thenReturn(self);
        when(accademicoService.trovaEmailUniClass(emailAltro)).thenReturn(altro);

        // Creiamo una lista di messaggi mista (Inviati, Ricevuti, Irrilevanti)
        List<Messaggio> tuttiIMessaggi = new ArrayList<>();

        // Messaggio 1: Inviato da ME a LUI (Dovrebbe finire in messaggiInviati)
        Messaggio mInviato = new Messaggio();
        mInviato.setAutore(self);
        mInviato.setDestinatario(altro);
        tuttiIMessaggi.add(mInviato);

        // Messaggio 2: Ricevuto da LUI per ME (Dovrebbe finire in messaggiRicevuti)
        Messaggio mRicevuto = new Messaggio();
        mRicevuto.setAutore(altro);
        mRicevuto.setDestinatario(self);
        tuttiIMessaggi.add(mRicevuto);

        // Messaggio 3: Irrilevante (tra due estranei) - Serve a testare che il filtro funzioni
        Accademico estraneo = new Accademico();
        estraneo.setMatricola("999999");
        Messaggio mIrrilevante = new Messaggio();
        mIrrilevante.setAutore(estraneo);
        mIrrilevante.setDestinatario(estraneo);
        tuttiIMessaggi.add(mIrrilevante);

        when(messaggioService.trovaTutti()).thenReturn(tuttiIMessaggi);

        // --- ACT (Esecuzione del metodo reale) ---
        servlet.doPost(request, response);

        // --- ASSERT (Verifiche) ---

        // 1. Verifichiamo che gli attributi siano stati settati nella Request
        verify(request).setAttribute(eq("messaggigi"), any(List.class));
        verify(request).setAttribute(eq("accademico"), eq(altro));
        verify(request).setAttribute(eq("messaggiInviati"), any(List.class));
        verify(request).setAttribute(eq("messaggiRicevuti"), any(List.class));
        verify(request).setAttribute(eq("accdemicoSelf"), eq(self));

        // 2. Verifichiamo che gli attributi siano stati settati nella Session
        verify(session).setAttribute(eq("messaggigi"), any(List.class));
        verify(session).setAttribute(eq("accademico"), eq(altro));
        verify(session).setAttribute(eq("accademicoSelf"), eq(self));

        // 3. Verifichiamo il redirect
        verify(response).sendRedirect("/UniClass/chat.jsp");

        // 4. Verifichiamo che i service siano stati chiamati
        verify(accademicoService).trovaEmailUniClass(emailSelf);
        verify(accademicoService).trovaEmailUniClass(emailAltro);
        verify(messaggioService).trovaTutti();
    }

    @Test
    void testDoPost() throws Exception {
        // --- ARRANGE ---
        String emailAltro = "docente@unisa.it";
        String emailSelf = "studente@studenti.unisa.it";
        String matricolaSelf = "0512100003";
        String matricolaAltro = "0512100004";

        when(request.getParameter("accademico")).thenReturn(emailAltro);
        when(request.getParameter("accademicoSelf")).thenReturn(emailSelf);
        when(request.getSession()).thenReturn(session);
        when(request.getContextPath()).thenReturn("/UniClass");

        Accademico self = new Accademico();
        self.setMatricola(matricolaSelf);
        self.setEmail(emailSelf);

        Accademico altro = new Accademico();
        altro.setMatricola(matricolaAltro);
        altro.setEmail(emailAltro);

        when(accademicoService.trovaEmailUniClass(emailSelf)).thenReturn(self);
        when(accademicoService.trovaEmailUniClass(emailAltro)).thenReturn(altro);

        List<Messaggio> messaggi = new ArrayList<>();
        when(messaggioService.trovaTutti()).thenReturn(messaggi);

        // --- ACT ---
        servlet.doPost(request, response);

        // --- ASSERT ---
        verify(response).sendRedirect("/UniClass/chat.jsp");
        verify(accademicoService, times(1)).trovaEmailUniClass(emailSelf);
        verify(accademicoService, times(1)).trovaEmailUniClass(emailAltro);
    }

    @Test
    void testDoGetWithMultipleMessages() throws Exception {
        // Test con più messaggi per aumentare la coverage
        String emailAltro = "prof@unisa.it";
        String emailSelf = "student@studenti.unisa.it";
        String matricolaSelf = "0512100005";
        String matricolaAltro = "0512100006";

        when(request.getParameter("accademico")).thenReturn(emailAltro);
        when(request.getParameter("accademicoSelf")).thenReturn(emailSelf);
        when(request.getSession()).thenReturn(session);
        when(request.getContextPath()).thenReturn("/UniClass");

        Accademico self = new Accademico();
        self.setMatricola(matricolaSelf);
        self.setEmail(emailSelf);

        Accademico altro = new Accademico();
        altro.setMatricola(matricolaAltro);
        altro.setEmail(emailAltro);

        when(accademicoService.trovaEmailUniClass(emailSelf)).thenReturn(self);
        when(accademicoService.trovaEmailUniClass(emailAltro)).thenReturn(altro);

        // Creiamo più messaggi per testare diversi scenari
        List<Messaggio> tuttiIMessaggi = new ArrayList<>();

        for (int i = 0; i < 5; i++) {
            Messaggio msg1 = new Messaggio();
            msg1.setAutore(self);
            msg1.setDestinatario(altro);
            tuttiIMessaggi.add(msg1);

            Messaggio msg2 = new Messaggio();
            msg2.setAutore(altro);
            msg2.setDestinatario(self);
            tuttiIMessaggi.add(msg2);
        }

        when(messaggioService.trovaTutti()).thenReturn(tuttiIMessaggi);

        // --- ACT ---
        servlet.doPost(request, response);

        // --- ASSERT ---
        verify(request).setAttribute(eq("messaggigi"), any(List.class));
        verify(request).setAttribute(eq("messaggiInviati"), any(List.class));
        verify(request).setAttribute(eq("messaggiRicevuti"), any(List.class));
        verify(response).sendRedirect("/UniClass/chat.jsp");
    }

    @Test
    void testDoGetWithEmptyMessageList() throws Exception {
        // Test con lista vuota di messaggi
        String emailAltro = "teacher@unisa.it";
        String emailSelf = "pupil@studenti.unisa.it";
        String matricolaSelf = "0512100007";
        String matricolaAltro = "0512100008";

        when(request.getParameter("accademico")).thenReturn(emailAltro);
        when(request.getParameter("accademicoSelf")).thenReturn(emailSelf);
        when(request.getSession()).thenReturn(session);
        when(request.getContextPath()).thenReturn("/UniClass");

        Accademico self = new Accademico();
        self.setMatricola(matricolaSelf);
        self.setEmail(emailSelf);

        Accademico altro = new Accademico();
        altro.setMatricola(matricolaAltro);
        altro.setEmail(emailAltro);

        when(accademicoService.trovaEmailUniClass(emailSelf)).thenReturn(self);
        when(accademicoService.trovaEmailUniClass(emailAltro)).thenReturn(altro);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());

        // --- ACT ---
        servlet.doPost(request, response);

        // --- ASSERT ---
        verify(request).setAttribute(eq("messaggigi"), any(List.class));
        verify(request).setAttribute(eq("messaggiInviati"), any(List.class));
        verify(request).setAttribute(eq("messaggiRicevuti"), any(List.class));
        verify(response).sendRedirect("/UniClass/chat.jsp");
    }

    @Test
    void testDoGetWithOnlyReceivedMessages() throws Exception {
        // Test con solo messaggi ricevuti
        String emailAltro = "sender@unisa.it";
        String emailSelf = "receiver@studenti.unisa.it";
        String matricolaSelf = "0512100009";
        String matricolaAltro = "0512100010";

        when(request.getParameter("accademico")).thenReturn(emailAltro);
        when(request.getParameter("accademicoSelf")).thenReturn(emailSelf);
        when(request.getSession()).thenReturn(session);
        when(request.getContextPath()).thenReturn("/UniClass");

        Accademico self = new Accademico();
        self.setMatricola(matricolaSelf);
        self.setEmail(emailSelf);

        Accademico altro = new Accademico();
        altro.setMatricola(matricolaAltro);
        altro.setEmail(emailAltro);

        when(accademicoService.trovaEmailUniClass(emailSelf)).thenReturn(self);
        when(accademicoService.trovaEmailUniClass(emailAltro)).thenReturn(altro);

        List<Messaggio> messaggi = new ArrayList<>();
        for (int i = 0; i < 3; i++) {
            Messaggio msg = new Messaggio();
            msg.setAutore(altro);
            msg.setDestinatario(self);
            messaggi.add(msg);
        }
        when(messaggioService.trovaTutti()).thenReturn(messaggi);

        // --- ACT ---
        servlet.doPost(request, response);

        // --- ASSERT ---
        verify(request).setAttribute(eq("messaggiRicevuti"), any(List.class));
        verify(response).sendRedirect("/UniClass/chat.jsp");
    }

    @Test
    void testDoGetWithOnlySentMessages() throws Exception {
        // Test con solo messaggi inviati
        String emailAltro = "recipient@unisa.it";
        String emailSelf = "sender@studenti.unisa.it";
        String matricolaSelf = "0512100011";
        String matricolaAltro = "0512100012";

        when(request.getParameter("accademico")).thenReturn(emailAltro);
        when(request.getParameter("accademicoSelf")).thenReturn(emailSelf);
        when(request.getSession()).thenReturn(session);
        when(request.getContextPath()).thenReturn("/UniClass");

        Accademico self = new Accademico();
        self.setMatricola(matricolaSelf);
        self.setEmail(emailSelf);

        Accademico altro = new Accademico();
        altro.setMatricola(matricolaAltro);
        altro.setEmail(emailAltro);

        when(accademicoService.trovaEmailUniClass(emailSelf)).thenReturn(self);
        when(accademicoService.trovaEmailUniClass(emailAltro)).thenReturn(altro);

        List<Messaggio> messaggi = new ArrayList<>();
        for (int i = 0; i < 3; i++) {
            Messaggio msg = new Messaggio();
            msg.setAutore(self);
            msg.setDestinatario(altro);
            messaggi.add(msg);
        }
        when(messaggioService.trovaTutti()).thenReturn(messaggi);

        // --- ACT ---
        servlet.doPost(request, response);

        // --- ASSERT ---
        verify(request).setAttribute(eq("messaggiInviati"), any(List.class));
        verify(response).sendRedirect("/UniClass/chat.jsp");
    }
}
