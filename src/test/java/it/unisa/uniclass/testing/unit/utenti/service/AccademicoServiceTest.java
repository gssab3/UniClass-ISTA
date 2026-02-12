package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.dao.AccademicoRemote;
import it.unisa.uniclass.testing.utils.TestUtils; // Import della utility
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.*;

import javax.naming.InitialContext;
import javax.naming.NamingException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class AccademicoServiceTest {

    @Mock
    private AccademicoRemote accademicoDao;

    private AccademicoService accademicoService;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        accademicoService = new AccademicoService(accademicoDao);
    }

    @Test
    void testCostruttoreDefault() throws Exception {
        try (MockedConstruction<InitialContext> mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/AccademicoDAO"))
                            .thenReturn(accademicoDao);
                })) {

            AccademicoService service = new AccademicoService();
            assertNotNull(service);
        }
    }

    @Test
    void testTrovaEmailUniClass_Esistente() {
        String email = "prof@unisa.it";
        Accademico acc = new Accademico();
        acc.setEmail(email);

        when(accademicoDao.trovaEmailUniClass(email)).thenReturn(acc);

        Accademico result = accademicoService.trovaEmailUniClass(email);
        assertNotNull(result);
        assertEquals(email, result.getEmail());
    }

    @Test
    void testTrovaEmailUniClass_NonTrovato() {
        String email = "fantasma@unisa.it";
        when(accademicoDao.trovaEmailUniClass(email)).thenThrow(new NoResultException());
        Accademico result = accademicoService.trovaEmailUniClass(email);
        assertNull(result);
    }

    @Test
    void testTrovaEmailPass_NullPassword() {
        String email = "prof@unisa.it";
        String pass = TestUtils.generateTestPassword(); // Dinamica
        Accademico acc = new Accademico();
        acc.setEmail(email);
        acc.setPassword(null);

        when(accademicoDao.trovaEmailUniClass(email)).thenReturn(acc);

        Accademico result = accademicoService.trovaEmailPassUniclass(email, pass);
        assertNotNull(result);
        assertEquals(email, result.getEmail());
    }

    @Test
    void testTrovaEmailPass_NoResultException() {
        String email = "fantasma@unisa.it";
        String pass = TestUtils.generateTestPassword();
        when(accademicoDao.trovaEmailUniClass(email)).thenThrow(new NoResultException());
        Accademico result = accademicoService.trovaEmailPassUniclass(email, pass);
        assertNull(result);
    }

    @Test
    void testTrovaAccademico_Esistente() {
        String matricola = "0512100001";
        Accademico expected = new Accademico();
        expected.setMatricola(matricola);
        when(accademicoDao.trovaAccademicoUniClass(matricola)).thenReturn(expected);
        Accademico result = accademicoService.trovaAccademicoUniClass(matricola);
        assertNotNull(result);
        assertEquals(matricola, result.getMatricola());
    }

    @Test
    void testTrovaAccademico_NonTrovato_GestioneEccezione() {
        when(accademicoDao.trovaAccademicoUniClass("999")).thenThrow(new NoResultException());
        Accademico result = accademicoService.trovaAccademicoUniClass("999");
        assertNull(result);
    }

    @Test
    void testTrovaEmailPass_Successo() {
        String email = "prof@unisa.it";
        // Sostituito "password123" con password generata
        String pass = TestUtils.generateTestPassword();
        Accademico acc = new Accademico();
        acc.setEmail(email);
        acc.setPassword(pass);

        when(accademicoDao.trovaEmailUniClass(email)).thenReturn(acc);

        Accademico result = accademicoService.trovaEmailPassUniclass(email, pass);
        assertNotNull(result);
        assertEquals(email, result.getEmail());
    }

    @Test
    void testTrovaEmailPass_PasswordErrata() {
        String email = "prof@unisa.it";
        Accademico acc = new Accademico();
        acc.setEmail(email);

        // Genero due password diverse dinamicamente
        String correctPass = TestUtils.generateTestPassword();
        String wrongPass = correctPass + "_ERR";

        acc.setPassword(correctPass); // Rimosso hardcoding e ggignore

        when(accademicoDao.trovaEmailUniClass(email)).thenReturn(acc);

        // Uso la password errata per il test
        Accademico result = accademicoService.trovaEmailPassUniclass(email, wrongPass);

        assertNull(result, "Deve ritornare null se la password non coincide");
    }

    @Test
    void testAggiungiAccademico() {
        Accademico nuovo = new Accademico();
        nuovo.setMatricola("0512109999");
        accademicoService.aggiungiAccademico(nuovo);
        verify(accademicoDao, times(1)).aggiungiAccademico(nuovo);
    }

    @Test
    void testMetodiCRUD_Passacarte() {
        accademicoService.trovaTuttiUniClass();
        verify(accademicoDao).trovaTuttiUniClass();

        accademicoService.trovaAttivati(true);
        verify(accademicoDao).trovaAttivati(true);

        accademicoService.retrieveEmail();
        verify(accademicoDao).retrieveEmail();

        Accademico a = new Accademico();
        accademicoService.rimuoviAccademico(a);
        verify(accademicoDao).rimuoviAccademico(a);

        accademicoService.cambiaAttivazione(a, true);
        verify(accademicoDao).cambiaAttivazione(a, true);
    }

    @Test
    void testCostruttoreDefault_NamingException() {
        try (var mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/AccademicoDAO"))
                            .thenThrow(new NamingException("Simulated JNDI error"));
                })) {

            RuntimeException ex = assertThrows(RuntimeException.class, AccademicoService::new);
            assertTrue(ex.getMessage().contains("Errore durante il lookup di AccademicoDAO"));
        }
    }

    @Test
    void testTrovaEmailPassUniclass_AccademicoNull() {
        AccademicoRemote dao = mock(AccademicoRemote.class);
        when(dao.trovaEmailUniClass("mail@unisa.it")).thenReturn(null);
        AccademicoService service = new AccademicoService(dao);
        Accademico result = service.trovaEmailPassUniclass("mail@unisa.it", "pwd");
        assertNull(result);
    }
}